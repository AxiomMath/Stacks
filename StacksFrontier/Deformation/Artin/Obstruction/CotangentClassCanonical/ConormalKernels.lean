module

public import StacksFrontier.Deformation.Artin.Infinitesimal.Functoriality
public import StacksFrontier.Deformation.Artin.Infinitesimal.LiftsAlong
public import StacksFrontier.Deformation.Artin.Obstruction.CotangentClass
public import StacksFrontier.Deformation.Artin.Obstruction.DualNotion
public import StacksFrontier.Deformation.Artin.Obstruction.CotangentClassCanonical.ConnectingMap

/-!
# The kernels and the splitting of the conormal sequence of deformation situations

The second part of `StacksFrontier.Deformation.Artin.Obstruction.CotangentClassCanonical`: the
kernels of the conormal sequence of deformation situations, their comparison with the conormal
module of a presentation, and the splitting of that sequence over `A[Ω_{A/Λ}]`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Pretriangulated NaiveCotangent
open ComplexShape (upIntRelNegOneZero)

namespace Deformation.Artin

universe u v w

attribute [local instance] HasDerivedCategory.standard

/-! ### The kernels of the conormal sequence of deformation situations -/

section Kernels

open CategoryTheory.Limits

variable {Λ A : Type u} [CommRing Λ] [CommRing A] [Algebra Λ A]

/-- The kernel of the projection `A[M] → A`, identified with `M`. -/
public def squareZeroExtKernelHom (M : ModuleCat.{u} A) :
    letI := Stacks.Smooth.kerModule (isDeformationSituation_squareZeroExt M).1
      (isDeformationSituation_squareZeroExt M).2
    ModuleCat.of A (RingHom.ker (squareZeroExtProj M)) ⟶ M :=
  letI := Stacks.Smooth.kerModule (isDeformationSituation_squareZeroExt M).1
    (isDeformationSituation_squareZeroExt M).2
  ModuleCat.ofHom (squareZeroExtKernelEquiv M).toLinearMap

/-- The module `M` identified with the kernel of the projection `A[M] → A`. -/
public def squareZeroExtKernelInv (M : ModuleCat.{u} A) :
    letI := Stacks.Smooth.kerModule (isDeformationSituation_squareZeroExt M).1
      (isDeformationSituation_squareZeroExt M).2
    M ⟶ ModuleCat.of A (RingHom.ker (squareZeroExtProj M)) :=
  letI := Stacks.Smooth.kerModule (isDeformationSituation_squareZeroExt M).1
    (isDeformationSituation_squareZeroExt M).2
  ModuleCat.ofHom (squareZeroExtKernelEquiv M).symm.toLinearMap

/-- The map `squareZeroExtKernelHom M` sends an element of the kernel of `A[M] → A` to its
component in `M`. -/
@[simp] public theorem squareZeroExtKernelHom_apply (M : ModuleCat.{u} A)
    (y : RingHom.ker (squareZeroExtProj M)) :
    (squareZeroExtKernelHom M).hom y = (y : squareZeroExt M).snd :=
  rfl

/-- The map `squareZeroExtKernelInv M` sends `v : M` to the element `(0, v)` of `A[M]`. -/
@[simp] public theorem squareZeroExtKernelInv_apply (M : ModuleCat.{u} A) (v : M) :
    ((squareZeroExtKernelInv M).hom v : squareZeroExt M) = TrivSqZeroExt.inr v :=
  rfl

/-- The two identifications of the kernel of `A[M] → A` with `M` are inverse. -/
@[simp] public theorem squareZeroExtKernelInv_comp_hom (M : ModuleCat.{u} A) :
    squareZeroExtKernelInv M ≫ squareZeroExtKernelHom M = 𝟙 M :=
  ModuleCat.hom_ext <| LinearMap.ext fun v =>
    congrArg TrivSqZeroExt.snd (squareZeroExtKernelInv_apply M v)

/-- The two identifications of the kernel of `A[M] → A` with `M` are inverse, in the other
order. -/
@[simp] public theorem squareZeroExtKernelHom_comp_inv (M : ModuleCat.{u} A) :
    letI := Stacks.Smooth.kerModule (isDeformationSituation_squareZeroExt M).1
      (isDeformationSituation_squareZeroExt M).2
    squareZeroExtKernelHom M ≫ squareZeroExtKernelInv M =
      𝟙 (ModuleCat.of A (RingHom.ker (squareZeroExtProj M))) := by
  let := Stacks.Smooth.kerModule (isDeformationSituation_squareZeroExt M).1
    (isDeformationSituation_squareZeroExt M).2
  exact ModuleCat.hom_ext <| LinearMap.ext (squareZeroExtKernelEquiv M).symm_apply_apply

/-- **The identification of the kernel of `A[M] → A` with `M` is an isomorphism.** -/
public instance isIso_squareZeroExtKernelHom (M : ModuleCat.{u} A) :
    IsIso (squareZeroExtKernelHom M) :=
  ⟨squareZeroExtKernelInv M, squareZeroExtKernelHom_comp_inv M,
    squareZeroExtKernelInv_comp_hom M⟩

/-- The conormal module `J/J²` identified with the kernel of `P/J² → A`. -/
public def infinitesimalKernelInv (E : Algebra.Extension.{u} Λ A) :
    letI := Stacks.Smooth.kerModule (isDeformationSituation_infinitesimal E).1
      (isDeformationSituation_infinitesimal E).2
    ModuleCat.of A E.Cotangent ⟶
      ModuleCat.of A (RingHom.ker (algebraMap E.infinitesimal.Ring A)) :=
  letI := Stacks.Smooth.kerModule (isDeformationSituation_infinitesimal E).1
    (isDeformationSituation_infinitesimal E).2
  ModuleCat.ofHom (infinitesimalKernelEquiv E).symm.toLinearMap

/-- **The identification of the kernel of `C → A` with the cotangent space of the presentation
is an isomorphism.** An element of the kernel has vanishing first component, so it is
determined by its second, and every element of the cotangent space occurs as a second
component. -/
public instance isIso_pushoutKernelHom (E : Algebra.Extension.{u} Λ A) :
    IsIso (pushoutKernelHom E) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  constructor
  · intro y z h
    have hy : (y : cotangentPushout E).fst = 0 := y.2
    have hz : (z : cotangentPushout E).fst = 0 := z.2
    exact Subtype.ext (TrivSqZeroExt.ext (hy.trans hz.symm) h)
  · intro v
    exact ⟨⟨TrivSqZeroExt.inr v, TrivSqZeroExt.fst_inr A v⟩, rfl⟩

/-- **The inverse of the identification of the kernel of `C → A` with the cotangent space**
sends `v` to `(0, v)`. Stated on elements: the inverse supplied by `isIso_pushoutKernelHom` is
`CategoryTheory.inv`, which no `rfl` reaches, so its one defining property has to be read off
the cancellation and the kernel condition. -/
public theorem pushoutKernelHom_inv_apply (E : Algebra.Extension.{u} Λ A)
    (v : cotangentSpaceModule E) :
    (((inv (pushoutKernelHom E)).hom v : RingHom.ker (cotangentPushoutProj E)) :
      cotangentPushout E) = TrivSqZeroExt.inr v := by
  have h1 : (pushoutKernelHom E).hom ((inv (pushoutKernelHom E)).hom v) = v := by
    rw [← ModuleCat.comp_apply, IsIso.inv_hom_id, ModuleCat.id_apply]
  have h2 : (((inv (pushoutKernelHom E)).hom v :
      RingHom.ker (cotangentPushoutProj E)) : cotangentPushout E).fst = 0 :=
    ((inv (pushoutKernelHom E)).hom v).2
  refine TrivSqZeroExt.ext ?_ ?_
  · rw [h2, TrivSqZeroExt.fst_inr]
  · rw [TrivSqZeroExt.snd_inr]
    exact h1

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) [IsLocallyNoetherian S]
variable (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A)))
variable (E : Algebra.Extension.{u} Λ A) (affineOpen : Spec (.of Λ) ⟶ S)
variable (hfact : Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ affineOpen = toS)

omit [IsLocallyNoetherian S] in
/-- **The map of kernels of the derivation-twisted surjection `C ⟶ C̄` is minus the conormal
surjection.** On the kernel the first component vanishes, so the derivation twist contributes
nothing and only the sign of the conormal surjection survives. -/
public theorem kernelMap_toDifferentialsTwisted
    (hC : B.Contains (Spec (.of (cotangentPushout E)))) (hft : Algebra.FiniteType Λ A) :
    letI := oppositeModule A (differentialsModule Λ A)
    letI := centralScalar A (differentialsModule Λ A)
    (cotangentPushoutToDifferentialsThickeningHom B S hS toS hA E hC hft affineOpen
          hfact).kernelMap ≫
        (squareZeroExtKernelHom (differentialsModule Λ A) :
          (differentialsBaseThickening B S hS toS hA hft affineOpen hfact).kernel ⟶
            differentialsModule Λ A) =
      pushoutKernelHom E ≫ (-ModuleCat.ofHom E.toKaehler) := by
  let := oppositeModule A (differentialsModule Λ A)
  let := centralScalar A (differentialsModule Λ A)
  refine kernelHom_ext B S hS toS hA
    (cotangentPushoutThickening B S hS toS hA E hC affineOpen hfact) _ fun y => ?_
  have hy : (y : cotangentPushout E).fst = 0 := y.2
  have hlhs : ((cotangentPushoutToDifferentialsThickeningHom B S hS toS hA E hC hft affineOpen
        hfact).kernelMap ≫
      (squareZeroExtKernelHom (differentialsModule Λ A) :
        (differentialsBaseThickening B S hS toS hA hft affineOpen hfact).kernel ⟶
          differentialsModule Λ A)).hom y =
      (cotangentPushoutToDifferentialsTwisted E (y : cotangentPushout E)).snd := rfl
  rw [hlhs, snd_cotangentPushoutToDifferentialsTwisted, hy, map_zero, zero_sub]
  rfl

omit [IsLocallyNoetherian S] in
/-- **The map of kernels of the derivation-twisted surjection `C ⟶ C̄`, solved for.** The
previous lemma read the map after the identification of `ker(C̄ → A)` with `Ω_{A/Λ}`; this one
reads it on its own, as minus the conormal surjection followed by that identification in the
other direction.

Stated here, beside `Deformation.Artin.kernelMap_toDifferentialsTwisted` and under the same
`letI` prologue, so that the `Module Aᵐᵒᵖ Ω[A⁄Λ]` and `IsCentralScalar A Ω[A⁄Λ]` instances
behind `C̄ = A[Ω_{A/Λ}]` resolve once for both: a caller that re-derives this identity in a
context with its own instances for those classes gets a statement that is definitionally equal
but not syntactically so, which `rw`, `cancel_mono` and `Mono` instance search cannot see
through even though function application can. -/
public theorem kernelMap_toDifferentialsTwisted_eq
    (hC : B.Contains (Spec (.of (cotangentPushout E)))) (hft : Algebra.FiniteType Λ A) :
    letI := oppositeModule A (differentialsModule Λ A)
    letI := centralScalar A (differentialsModule Λ A)
    (cotangentPushoutToDifferentialsThickeningHom B S hS toS hA E hC hft affineOpen
        hfact).kernelMap =
      pushoutKernelHom E ≫
        (-(ModuleCat.ofHom E.toKaehler ≫
          (squareZeroExtKernelInv (differentialsModule Λ A) :
            differentialsModule Λ A ⟶
              (differentialsBaseThickening B S hS toS hA hft affineOpen hfact).kernel))) := by
  let := oppositeModule A (differentialsModule Λ A)
  let := centralScalar A (differentialsModule Λ A)
  have h := kernelMap_toDifferentialsTwisted B S hS toS hA E affineOpen hfact hC hft
  refine ((Category.comp_id _).symm.trans
    (congrArg _ (squareZeroExtKernelHom_comp_inv _).symm)).trans
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h).trans ?_))
  exact (Category.assoc _ _ _).trans (congrArg _ (Preadditive.neg_comp _ _))

omit [IsLocallyNoetherian S] in
/-- **The map of kernels of the inclusion `C' ⟶ C` carries the conormal module `J/J²` to the
differential of the naive cotangent complex of the presentation.** The conormal module is the
kernel of `P/J² → A`, which maps into the kernel of `C' → A` and on to the kernel of `C → A`,
where it becomes the differential. -/
public theorem infinitesimalKernelInv_comp_kernelMap
    (hE : B.Contains (Spec (.of E.Ring)))
    (hC : B.Contains (Spec (.of (cotangentPushout E)))) :
    (infinitesimalKernelInv E :
          ModuleCat.of A E.Cotangent ⟶
            (infinitesimalThickening B S hS toS hA E hE affineOpen hfact).kernel) ≫
          (infinitesimalToPushoutImageHom B S hS toS hA E hE hC affineOpen hfact).kernelMap ≫
        (cotangentPushoutImageToPushoutHom B S hS toS hA E hC affineOpen hfact).kernelMap ≫
          pushoutKernelHom E =
      ModuleCat.ofHom E.cotangentComplex := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  have h := squareZeroExtKernelEquiv_kerRestrict_infinitesimal E
    ((infinitesimalKernelEquiv E).symm c)
  rw [(infinitesimalKernelEquiv E).apply_symm_apply] at h
  exact h

omit [IsLocallyNoetherian S] in
/-- **The conormal module, carried into the kernel of `C → A`, is the differential.** Stated on
elements, as `(0, d c)`: this is `infinitesimalKernelInv_comp_kernelMap` with the last
identification removed, which is the form the comparison of the two-term complex with the
conormal kernel sequence is checked in. -/
public theorem conormalComparison_apply (hE : B.Contains (Spec (.of E.Ring)))
    (hC : B.Contains (Spec (.of (cotangentPushout E)))) (c : E.Cotangent) :
    ((((infinitesimalKernelInv E :
            ModuleCat.of A E.Cotangent ⟶
              (infinitesimalThickening B S hS toS hA E hE affineOpen hfact).kernel) ≫
          (infinitesimalToPushoutImageHom B S hS toS hA E hE hC affineOpen hfact).kernelMap ≫
            (cotangentPushoutImageToPushoutHom B S hS toS hA E hC affineOpen
              hfact).kernelMap).hom c : RingHom.ker (cotangentPushoutProj E)) :
        cotangentPushout E) = TrivSqZeroExt.inr (E.cotangentComplex c) := by
  have hsnd := congrArg (fun m => m.hom c)
    (infinitesimalKernelInv_comp_kernelMap B S hS toS hA E affineOpen hfact hE hC)
  refine TrivSqZeroExt.ext ?_ ?_
  · rw [TrivSqZeroExt.fst_inr]
    exact (((infinitesimalKernelInv E :
      ModuleCat.of A E.Cotangent ⟶
        (infinitesimalThickening B S hS toS hA E hE affineOpen hfact).kernel) ≫
        (infinitesimalToPushoutImageHom B S hS toS hA E hE hC affineOpen hfact).kernelMap ≫
          (cotangentPushoutImageToPushoutHom B S hS toS hA E hC affineOpen
            hfact).kernelMap).hom c).2
  · rw [TrivSqZeroExt.snd_inr]
    exact hsnd

omit [IsLocallyNoetherian S] in
/-- **The kernel sequence of the conormal sequence of deformation situations is a complex.**
The map of kernels of the inclusion `C' ⟶ C` followed by the map of kernels of the
derivation-twisted surjection `C ⟶ C̄` is zero.

On elements this is the computation that an element `y` of `ker(C' → A)` has
`E.toKaehler y.snd = 0`: such a `y` is the image of a class `g + J²` with `g` in the kernel
`J` of the presentation, so `y.snd` is the differential `d g` of the naive cotangent complex
and the conormal surjection kills it. The same derivation occurs inside
`Deformation.Artin.isShortExactSequence_cotangentPushoutToDifferentialsTwisted`, where it
proves exactness in the middle; stated on its own it is what makes the short complex of
kernels available without the boundary condition (iv), which is what the comparison of the
two-term complex of a presentation with that sequence needs. -/
public theorem kernelMap_comp_kernelMap_eq_zero
    (hC : B.Contains (Spec (.of (cotangentPushout E)))) (hft : Algebra.FiniteType Λ A) :
    letI := oppositeModule A (differentialsModule Λ A)
    letI := centralScalar A (differentialsModule Λ A)
    (cotangentPushoutImageToPushoutHom B S hS toS hA E hC affineOpen hfact).kernelMap ≫
        (cotangentPushoutToDifferentialsThickeningHom B S hS toS hA E hC hft affineOpen
          hfact).kernelMap = 0 := by
  let := oppositeModule A (differentialsModule Λ A)
  let := centralScalar A (differentialsModule Λ A)
  refine kernelHom_ext B S hS toS hA
    (cotangentPushoutImageThickening B S hS toS hA E
      (cotangentPushoutImage_mem_site E B hC) affineOpen hfact) _ fun y => ?_
  refine Subtype.ext ?_
  have hy : ((y : cotangentPushoutImage E) : cotangentPushout E).fst = 0 := y.2
  obtain ⟨w, hw⟩ := RingHom.mem_range.1 (y : cotangentPushoutImage E).2
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective w
  have hgy : cotangentPushoutFun E g =
      ((y : cotangentPushoutImage E) : cotangentPushout E) := by
    rw [← hw, cotangentPushoutInfinitesimalMap_mk, cotangentPushoutMap_apply]
  have hg : algebraMap E.Ring A g = 0 := by
    rw [← cotangentPushoutFun_fst E g, hgy]
    exact hy
  have hsnd : ((y : cotangentPushoutImage E) : cotangentPushout E).snd =
      E.cotangentComplex (Algebra.Extension.Cotangent.mk ⟨g, hg⟩) := by
    rw [Algebra.Extension.cotangentComplex_mk, ← cotangentPushoutFun_snd E g, hgy]
  have hzero : E.toKaehler ((y : cotangentPushoutImage E) : cotangentPushout E).snd = 0 :=
    (toKaehler_eq_zero_iff E _).2 ⟨Algebra.Extension.Cotangent.mk ⟨g, hg⟩, hsnd.symm⟩
  change cotangentPushoutToDifferentialsTwisted E
    ((y : cotangentPushoutImage E) : cotangentPushout E) = 0
  refine TrivSqZeroExt.ext ?_ ?_
  · rw [fst_cotangentPushoutToDifferentialsTwisted, hy, TrivSqZeroExt.fst_zero]
  · rw [snd_cotangentPushoutToDifferentialsTwisted, hy, map_zero, hzero, sub_zero,
      TrivSqZeroExt.snd_zero]

omit [IsLocallyNoetherian S] in
/-- **The two-term complex of a presentation maps to the conormal kernel sequence.** All the
data the long exact sequence of the conormal sequence of deformation situations needs, for the
two-term complex `NL(α)` of a presentation `P` of `A` over `Λ`: a map `a` of the conormal
module into `ker(C' → A)`, a map `b` of the cotangent space into `ker(C → A)` with
`a ≫ f + d ≫ b = 0`, the resulting projection `w` of the degree-zero term onto
`ker(C̄ → A)`, and the comparison `proj` of `NL_{A/Λ}` with `ker(C̄ → A)[0]` it induces.

The witnesses are the conormal identification of `ker(C' → A)` and minus the inverse of the
identification of `ker(C → A)` with the cotangent space, so that `_hab` is
`Deformation.Artin.conormalComparison_apply` against
`Deformation.Artin.pushoutKernelHom_inv_apply`, and `w` is literally `b` followed by the map
of kernels of `C ⟶ C̄`, which is what makes the last conjunct — that `w` computes the
presentation-level projection onto `Ω_{A/Λ}` — the content of
`Deformation.Artin.kernelMap_toDifferentialsTwisted_eq`.

Everything is packaged into one existential statement, under one `letI` prologue for the
`Module Aᵐᵒᵖ Ω[A⁄Λ]` and `IsCentralScalar A Ω[A⁄Λ]` instances behind `C̄ = A[Ω_{A/Λ}]`, so
that a consumer never has to write a morphism into `ker(C̄ → A)` itself: such a morphism
mentions `Deformation.Artin.squareZeroExtKernelInv`, whose type carries those instances, and a
consumer carrying its own copies of them gets a term definitionally equal to but syntactically
different from the one baked into the type of
`Deformation.Artin.differentialsBaseThickening`. -/
public theorem exists_conormalKernelComparison {ι : Type u} (P : Algebra.Generators Λ A ι)
    (φ : P.Hom (canonicalGenerators Λ A))
    (hE : B.Contains (Spec (.of P.toExtension.Ring)))
    (hC : B.Contains (Spec (.of (cotangentPushout P.toExtension))))
    (hft : Algebra.FiniteType Λ A) :
    letI := oppositeModule A (differentialsModule Λ A)
    letI := centralScalar A (differentialsModule Λ A)
    ∃ (a : ModuleCat.of A (nlRestrict A P).X₁ ⟶
          (cotangentPushoutImageThickening B S hS toS hA P.toExtension
            (cotangentPushoutImage_mem_site P.toExtension B hC) affineOpen hfact).kernel)
        (b : ModuleCat.of A (nlRestrict A P).X₀ ⟶
          (cotangentPushoutThickening B S hS toS hA P.toExtension hC affineOpen hfact).kernel)
        (_hab : a ≫ (cotangentPushoutImageToPushoutHom B S hS toS hA P.toExtension hC
              affineOpen hfact).kernelMap +
            ModuleCat.ofHom (nlRestrict A P).d ≫ b = 0)
        (w : ModuleCat.of A (nlRestrict A P).X₀ ⟶
          (differentialsBaseThickening B S hS toS hA hft affineOpen hfact).kernel)
        (hdw : ModuleCat.ofHom (nlRestrict A P).d ≫ w = 0)
        (_hwg : b ≫ (cotangentPushoutToDifferentialsThickeningHom B S hS toS hA P.toExtension
            hC hft affineOpen hfact).kernelMap = w)
        (_hk : ∀ x : P.toExtension.ker,
          (((a.hom (Algebra.Extension.Cotangent.mk x) :
                RingHom.ker (cotangentPushoutImageProj P.toExtension)) :
              cotangentPushoutImage P.toExtension) : cotangentPushout P.toExtension) =
            cotangentPushoutMap P.toExtension x.1)
        (proj : derivedNaiveCotangentComplex Λ A ⟶
          (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
            (differentialsBaseThickening B S hS toS hA hft affineOpen hfact).kernel)
        (ker : (differentialsBaseThickening B S hS toS hA hft affineOpen hfact).kernel ⟶
          differentialsModule Λ A),
      (derivedNaiveCotangentComplexIso Λ A P φ).hom ≫ proj =
          DerivedCategory.Q.map (twoTermToSingle w hdw) ∧
        twoTermToSingle w hdw =
            presentationToDifferentials P ≫
              (HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) 0).map
                (squareZeroExtKernelInv (differentialsModule Λ A) :
                  differentialsModule Λ A ⟶
                    (differentialsBaseThickening B S hS toS hA hft affineOpen
                      hfact).kernel) ∧
          proj ≫ (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map ker =
              naiveCotangentToDifferentials Λ A ∧
            (cotangentPushoutToDifferentialsThickeningHom B S hS toS hA P.toExtension hC hft
                  affineOpen hfact).kernelMap ≫ ker =
                (-(pushoutKernelHom P.toExtension)) ≫
                  ModuleCat.ofHom P.toExtension.toKaehler ∧
              (squareZeroExtKernelInv (differentialsModule Λ A) :
                    differentialsModule Λ A ⟶
                      (differentialsBaseThickening B S hS toS hA hft affineOpen
                        hfact).kernel) ≫ ker =
                𝟙 (differentialsModule Λ A) := by
  let := oppositeModule A (differentialsModule Λ A)
  let := centralScalar A (differentialsModule Λ A)
  have h0 : ModuleCat.ofHom (nlRestrict A P).d ≫
      ModuleCat.ofHom P.toExtension.toKaehler = 0 :=
    ModuleCat.hom_ext <| LinearMap.ext
      P.toExtension.exact_cotangentComplex_toKaehler.apply_apply_eq_zero
  have hwg0 : ModuleCat.ofHom (nlRestrict A P).d ≫
      (ModuleCat.ofHom P.toExtension.toKaehler ≫
        (squareZeroExtKernelInv (differentialsModule Λ A) :
          differentialsModule Λ A ⟶
            (differentialsBaseThickening B S hS toS hA hft affineOpen hfact).kernel)) = 0 := by
    rw [← Category.assoc, h0, Limits.zero_comp]
  have hw : (-(inv (pushoutKernelHom P.toExtension))) ≫
        (cotangentPushoutToDifferentialsThickeningHom B S hS toS hA P.toExtension hC hft
          affineOpen hfact).kernelMap =
      ModuleCat.ofHom P.toExtension.toKaehler ≫
        (squareZeroExtKernelInv (differentialsModule Λ A) :
          differentialsModule Λ A ⟶
            (differentialsBaseThickening B S hS toS hA hft affineOpen hfact).kernel) := by
    rw [kernelMap_toDifferentialsTwisted_eq B S hS toS hA P.toExtension affineOpen hfact hC hft]
    exact (Preadditive.neg_comp _ _).trans
      ((congrArg Neg.neg (IsIso.inv_hom_id_assoc _ _)).trans (neg_neg _))
  have hgoal : twoTermToSingle (T := nlRestrict A P)
        (ModuleCat.ofHom P.toExtension.toKaehler ≫
          (squareZeroExtKernelInv (differentialsModule Λ A) :
            differentialsModule Λ A ⟶
              (differentialsBaseThickening B S hS toS hA hft affineOpen hfact).kernel))
          hwg0 =
      presentationToDifferentials P ≫
        (HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) 0).map
          (squareZeroExtKernelInv (differentialsModule Λ A) :
            differentialsModule Λ A ⟶
              (differentialsBaseThickening B S hS toS hA hft affineOpen hfact).kernel) := by
    rw [presentationToDifferentials_eq P]
    exact twoTermToSingle_comp _ _ _ hwg0
  have hinvker : (squareZeroExtKernelInv (differentialsModule Λ A) :
        differentialsModule Λ A ⟶
          (differentialsBaseThickening B S hS toS hA hft affineOpen hfact).kernel) ≫
      (squareZeroExtKernelHom (differentialsModule Λ A) :
        (differentialsBaseThickening B S hS toS hA hft affineOpen hfact).kernel ⟶
          differentialsModule Λ A) = 𝟙 (differentialsModule Λ A) :=
    squareZeroExtKernelInv_comp_hom (differentialsModule Λ A)
  have hkerg : (cotangentPushoutToDifferentialsThickeningHom B S hS toS hA P.toExtension hC hft
        affineOpen hfact).kernelMap ≫
      (squareZeroExtKernelHom (differentialsModule Λ A) :
        (differentialsBaseThickening B S hS toS hA hft affineOpen hfact).kernel ⟶
          differentialsModule Λ A) =
      (-(pushoutKernelHom P.toExtension)) ≫ ModuleCat.ofHom P.toExtension.toKaehler := by
    rw [Preadditive.neg_comp]
    exact (kernelMap_toDifferentialsTwisted B S hS toS hA P.toExtension affineOpen hfact hC
      hft).trans (Preadditive.comp_neg _ _)
  have hts : twoTermToSingle (T := nlRestrict A P)
        (ModuleCat.ofHom P.toExtension.toKaehler ≫
          (squareZeroExtKernelInv (differentialsModule Λ A) :
            differentialsModule Λ A ⟶
              (differentialsBaseThickening B S hS toS hA hft affineOpen hfact).kernel))
          hwg0 ≫
      (HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) 0).map
        (squareZeroExtKernelHom (differentialsModule Λ A) :
          (differentialsBaseThickening B S hS toS hA hft affineOpen hfact).kernel ⟶
            differentialsModule Λ A) =
      presentationToDifferentials P := by
    rw [hgoal, Category.assoc, ← Functor.map_comp, hinvker, CategoryTheory.Functor.map_id,
      Category.comp_id]
  have hkerproj : ((derivedNaiveCotangentComplexIso Λ A P φ).inv ≫
        DerivedCategory.Q.map (twoTermToSingle (T := nlRestrict A P)
          (ModuleCat.ofHom P.toExtension.toKaehler ≫
            (squareZeroExtKernelInv (differentialsModule Λ A) :
              differentialsModule Λ A ⟶
                (differentialsBaseThickening B S hS toS hA hft affineOpen hfact).kernel))
            hwg0)) ≫
      (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map
        (squareZeroExtKernelHom (differentialsModule Λ A) :
          (differentialsBaseThickening B S hS toS hA hft affineOpen hfact).kernel ⟶
            differentialsModule Λ A) =
      naiveCotangentToDifferentials Λ A := by
    have h1 : DerivedCategory.Q.map (twoTermToSingle (T := nlRestrict A P)
          (ModuleCat.ofHom P.toExtension.toKaehler ≫
            (squareZeroExtKernelInv (differentialsModule Λ A) :
              differentialsModule Λ A ⟶
                (differentialsBaseThickening B S hS toS hA hft affineOpen hfact).kernel))
            hwg0) ≫
        (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map
          (squareZeroExtKernelHom (differentialsModule Λ A) :
            (differentialsBaseThickening B S hS toS hA hft affineOpen hfact).kernel ⟶
              differentialsModule Λ A) =
        DerivedCategory.Q.map (presentationToDifferentials P) := by
      change DerivedCategory.Q.map (twoTermToSingle (T := nlRestrict A P)
          (ModuleCat.ofHom P.toExtension.toKaehler ≫
            (squareZeroExtKernelInv (differentialsModule Λ A) :
              differentialsModule Λ A ⟶
                (differentialsBaseThickening B S hS toS hA hft affineOpen hfact).kernel))
            hwg0) ≫
        DerivedCategory.Q.map ((HomologicalComplex.single (ModuleCat.{u} A)
          (ComplexShape.up ℤ) 0).map
            (squareZeroExtKernelHom (differentialsModule Λ A) :
              (differentialsBaseThickening B S hS toS hA hft affineOpen hfact).kernel ⟶
                differentialsModule Λ A)) = _
      rw [← Functor.map_comp, hts]
    rw [Category.assoc, h1,
      ← derivedNaiveCotangentComplexIso_hom_comp_naiveCotangentToDifferentials,
      Iso.inv_hom_id_assoc]
  refine ⟨infinitesimalKernelInv P.toExtension ≫
      (infinitesimalToPushoutImageHom B S hS toS hA P.toExtension hE hC affineOpen
        hfact).kernelMap,
    -(inv (pushoutKernelHom P.toExtension)), ?_,
    ModuleCat.ofHom P.toExtension.toKaehler ≫
      (squareZeroExtKernelInv (differentialsModule Λ A) :
        differentialsModule Λ A ⟶
          (differentialsBaseThickening B S hS toS hA hft affineOpen hfact).kernel),
    hwg0, hw, ?_,
    (derivedNaiveCotangentComplexIso Λ A P φ).inv ≫
      DerivedCategory.Q.map (twoTermToSingle _ hwg0),
    (squareZeroExtKernelHom (differentialsModule Λ A) :
      (differentialsBaseThickening B S hS toS hA hft affineOpen hfact).kernel ⟶
        differentialsModule Λ A),
    Iso.hom_inv_id_assoc _ _, hgoal, hkerproj, hkerg, hinvker⟩
  · let := (cotangentPushoutThickening B S hS toS hA P.toExtension hC affineOpen
      hfact).kernel.isModule
    refine ModuleCat.hom_ext (LinearMap.ext fun c => Subtype.ext ?_)
    have h1 := conormalComparison_apply B S hS toS hA P.toExtension affineOpen hfact hE hC c
    have h2 := pushoutKernelHom_inv_apply P.toExtension (P.toExtension.cotangentComplex c)
    change (((infinitesimalKernelInv P.toExtension ≫
              (infinitesimalToPushoutImageHom B S hS toS hA P.toExtension hE hC affineOpen
                hfact).kernelMap ≫
                (cotangentPushoutImageToPushoutHom B S hS toS hA P.toExtension hC affineOpen
                  hfact).kernelMap).hom c :
            RingHom.ker (cotangentPushoutProj P.toExtension)) :
          cotangentPushout P.toExtension) +
        -(((inv (pushoutKernelHom P.toExtension)).hom
              (P.toExtension.cotangentComplex c) :
            RingHom.ker (cotangentPushoutProj P.toExtension)) :
          cotangentPushout P.toExtension) = 0
    rw [h1, h2, add_neg_cancel]
  · intro x
    have hx : (infinitesimalKernelEquiv P.toExtension).symm
          (Algebra.Extension.Cotangent.mk x) =
        ⟨Ideal.Quotient.mk (P.toExtension.ker ^ 2) x.1,
          quotient_mk_mem_ker_infinitesimal P.toExtension x⟩ := by
      rw [LinearEquiv.symm_apply_eq]
      exact (infinitesimalKernelEquiv_mk P.toExtension x).symm
    change cotangentPushoutInfinitesimalMap P.toExtension
        (((infinitesimalKernelEquiv P.toExtension).symm
          (Algebra.Extension.Cotangent.mk x) :
            RingHom.ker (algebraMap P.toExtension.infinitesimal.Ring A)) :
          P.toExtension.infinitesimal.Ring) =
      cotangentPushoutMap P.toExtension x.1
    rw [hx]
    exact cotangentPushoutInfinitesimalMap_mk P.toExtension x.1

end Kernels

/-! ### The splitting of the conormal sequence of deformation situations -/

section BoundarySplitting

open TensorProduct

variable {Λ A : Type u} [CommRing Λ] [CommRing A] [Algebra Λ A]

/-- **The conormal surjection carries the universal derivation of the presentation ring to the
universal derivation of `A`.** -/
public theorem toKaehler_one_tmul_D (E : Algebra.Extension.{u} Λ A) (f : E.Ring) :
    E.toKaehler ((1 : A) ⊗ₜ[E.Ring] KaehlerDifferential.D Λ E.Ring f) =
      KaehlerDifferential.D Λ A (algebraMap E.Ring A f) := by
  rw [Algebra.Extension.toKaehler, KaehlerDifferential.mapBaseChange_tmul, one_smul,
    KaehlerDifferential.map_D]

/-- **The derivation-twisted surjection `C ⟶ C̄` kills the conormal image of the presentation.**
The canonical map `f ↦ (α f, df ⊗ 1)` of the presentation into the pushout algebra is carried
to the section `α f ↦ (α f, 0)`, the derivation twist cancelling the conormal image of `df`
exactly. -/
public theorem cotangentPushoutToDifferentialsTwisted_map (E : Algebra.Extension.{u} Λ A)
    (f : E.Ring) :
    letI := oppositeModule A (differentialsModule Λ A)
    letI := centralScalar A (differentialsModule Λ A)
    cotangentPushoutToDifferentialsTwisted E (cotangentPushoutMap E f) =
      TrivSqZeroExt.inl (algebraMap E.Ring A f) := by
  let := oppositeModule A (differentialsModule Λ A)
  let := centralScalar A (differentialsModule Λ A)
  refine TrivSqZeroExt.ext ?_ ?_
  · rw [fst_cotangentPushoutToDifferentialsTwisted, cotangentPushoutMap_apply,
      cotangentPushoutFun_fst, TrivSqZeroExt.fst_inl]
  · rw [snd_cotangentPushoutToDifferentialsTwisted, cotangentPushoutMap_apply,
      cotangentPushoutFun_fst, cotangentPushoutFun_snd, toKaehler_one_tmul_D, sub_self,
      TrivSqZeroExt.snd_inl]

/-- **The splitting of the conormal short exact sequence of deformation situations is the
section of `C̄ = A[Ω_{A/Λ}]`.** A ring map `s : A → C̄` factoring the composite
`C' ↪ C ⟶ C̄` through `C' → A` is `a ↦ (a, 0)`: the composite kills the conormal image of the
presentation, and `C' → A` is surjective. -/
public theorem eq_inlHom_of_comp_cotangentPushoutToDifferentialsTwisted
    (E : Algebra.Extension.{u} Λ A) :
    letI := oppositeModule A (differentialsModule Λ A)
    letI := centralScalar A (differentialsModule Λ A)
    ∀ s : A →+* squareZeroExt (differentialsModule Λ A),
      (cotangentPushoutToDifferentialsTwisted E).comp
          (cotangentPushoutImage E).subtype =
        s.comp (cotangentPushoutImageProj E) →
      s = TrivSqZeroExt.inlHom A (differentialsModule Λ A) := by
  let := oppositeModule A (differentialsModule Λ A)
  let := centralScalar A (differentialsModule Λ A)
  intro s hs
  refine RingHom.ext fun a => ?_
  obtain ⟨f, hf⟩ := E.algebraMap_surjective a
  let y : cotangentPushoutImage E :=
    ⟨cotangentPushoutMap E f,
      RingHom.mem_range.2 ⟨Ideal.Quotient.mk (E.ker ^ 2) f, rfl⟩⟩
  have hya : cotangentPushoutImageProj E y = a := by
    change cotangentPushoutProj E (cotangentPushoutMap E f) = a
    rw [cotangentPushoutMap_apply, show cotangentPushoutProj E (cotangentPushoutFun E f) =
      (cotangentPushoutFun E f).fst from rfl, cotangentPushoutFun_fst, hf]
  have h := congrArg (fun g : cotangentPushoutImage E →+* squareZeroExt
    (differentialsModule Λ A) => g y) hs
  simp only [RingHom.comp_apply, hya] at h
  rw [← h]
  change cotangentPushoutToDifferentialsTwisted E (cotangentPushoutMap E f) = _
  rw [cotangentPushoutToDifferentialsTwisted_map, hf]
  rfl

/-- **The section of the pushout algebra, followed by the map `ψ : C ⟶ A[I₁]` of the boundary
condition and the identification of `I₁ = ker(C̄ → A)` with `Ω_{A/Λ}`, is the canonical section
`a ↦ (a, d a)` of 07YC.** The map `ψ` is prescribed by the boundary condition up to the
splitting, which is the section of `C̄` by
`Deformation.Artin.eq_inlHom_of_comp_cotangentPushoutToDifferentialsTwisted`, so on the section
of `C` it is the derivation-twisted surjection itself, whose value there is `(a, d a)`. -/
public theorem squareZeroExtMap_kernelHom_psi_section (E : Algebra.Extension.{u} Λ A)
    (ψ : letI := oppositeModule A (differentialsModule Λ A)
      letI := centralScalar A (differentialsModule Λ A)
      cotangentPushout E →+*
        squareZeroExt
          (ModuleCat.of A (RingHom.ker (squareZeroExtProj (differentialsModule Λ A)))))
    (hψfst : letI := oppositeModule A (differentialsModule Λ A)
      letI := centralScalar A (differentialsModule Λ A)
      ∀ y : cotangentPushout E, (ψ y).fst = cotangentPushoutProj E y)
    (hψsnd : letI := oppositeModule A (differentialsModule Λ A)
      letI := centralScalar A (differentialsModule Λ A)
      ∀ y : cotangentPushout E,
        ((ψ y).snd : squareZeroExt (differentialsModule Λ A)) =
          cotangentPushoutToDifferentialsTwisted E y -
            TrivSqZeroExt.inl (cotangentPushoutProj E y))
    (a : A) :
    letI := oppositeModule A (differentialsModule Λ A)
    letI := centralScalar A (differentialsModule Λ A)
    squareZeroExtMap (squareZeroExtKernelHom (differentialsModule Λ A))
        (ψ (cotangentPushoutSection E a)) =
      TrivSqZeroExt.inl a + TrivSqZeroExt.inr (KaehlerDifferential.D Λ A a) := by
  let := oppositeModule A (differentialsModule Λ A)
  let := centralScalar A (differentialsModule Λ A)
  have hfst : cotangentPushoutProj E (cotangentPushoutSection E a) = a :=
    TrivSqZeroExt.fst_inl A a
  have hsnd : ((ψ (cotangentPushoutSection E a)).snd :
      squareZeroExt (differentialsModule Λ A)) =
      TrivSqZeroExt.inr (KaehlerDifferential.D Λ A a) := by
    rw [hψsnd, cotangentPushoutToDifferentialsTwisted_section, hfst]
    abel
  refine TrivSqZeroExt.ext ?_ ?_
  · rw [fst_squareZeroExtMap, hψfst, hfst, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl,
      TrivSqZeroExt.fst_inr, add_zero]
  · rw [snd_squareZeroExtMap, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl,
      TrivSqZeroExt.snd_inr, zero_add]
    change (((ψ (cotangentPushoutSection E a)).snd : squareZeroExt
      (differentialsModule Λ A))).snd = _
    rw [hsnd, TrivSqZeroExt.snd_inr]

end BoundarySplitting

end Deformation.Artin

end
