module

public import StacksFrontier.Deformation.Artin.Infinitesimal.Functoriality
public import StacksFrontier.Deformation.Artin.Infinitesimal.LiftsAlong
public import StacksFrontier.Deformation.Artin.Obstruction.CotangentClass
public import StacksFrontier.Deformation.Artin.Obstruction.DualNotion
public import StacksFrontier.Deformation.Artin.Obstruction.CotangentClassCanonical.ConnectingMap
public import StacksFrontier.Deformation.Artin.Obstruction.CotangentClassCanonical.ConormalKernels

/-!
# The canonical element and the cotangent obstruction class

The third part of `StacksFrontier.Deformation.Artin.Obstruction.CotangentClassCanonical`: lifts
along a retracting thickening and the canonical element, the evaluation of a class on a
presentation, the obstruction of `C'` as the boundary of the canonical element, and the
existence of the cotangent obstruction class (Stacks 07YY).
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Pretriangulated NaiveCotangent
open ComplexShape (upIntRelNegOneZero)

namespace Deformation.Artin

universe u v w

attribute [local instance] HasDerivedCategory.standard

/-! ### Lifts along a retracting thickening, and the canonical element -/

section Retraction

variable (A : Type u) [CommRing A] (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A)))
variable {X : Type v} [Category.{w} X] (p : X ⥤ BigFppfOver B S hS) (x : X)
  (hx : p.obj x = algebraOver A B S hS toS hA) (hp : p.IsFiberedInGroupoids)

/-- Pulling a lift back along a map of base thickenings gives a lift with a strongly cartesian
arrow over that map, compatible with the structure arrows. -/
private theorem exists_cartesian_pullbackFiber (hp' : p.IsFiberedInGroupoids)
    [(Under.post p : Under x ⥤ Under (p.obj x)).IsFibered] {a b : Under (p.obj x)} (g : a ⟶ b)
    (L : (Under.post p).Fiber b) :
    ∃ c : (Functor.pullbackFiber (Under.post p) L g).1.right ⟶ L.1.right,
      p.IsStronglyCartesian g.right c ∧
        (Functor.pullbackFiber (Under.post p) L g).1.hom ≫ c = L.1.hom := by
  let u : (Functor.pullbackFiber (Under.post p) L g).1 ⟶ L.1 :=
    Functor.IsPreFibered.pullbackMap L.2 g
  have hu : (Under.post p).IsCartesian g u := Functor.IsPreFibered.pullbackMap.IsCartesian L.2 g
  have : p.IsHomLift g.right u.right := underPost_isHomLift_right p g u hu.toIsHomLift
  exact ⟨u.right, hp'.isStronglyCartesian_homLift _ _, Under.w u⟩

include hp in
/-- **The lift of `x` along a retracting thickening carries a strongly cartesian arrow back to
`x` over the retraction, of which its structure arrow is a section.** This is the content of
`Deformation.Artin.liftOfRetraction` read in the ambient category rather than in the lifts:
the chosen pullback arrow lies over the retraction, so it is strongly cartesian because the
category is fibred in groupoids, and it commutes with the structure arrows because it is a
morphism of lifts. -/
public theorem exists_cartesian_liftOfRetraction {Y : BigFppfOver B S hS}
    (a : algebraOver A B S hS toS hA ⟶ Y) (r : Y ⟶ algebraOver A B S hS toS hA)
    (ha : a ≫ r = 𝟙 (algebraOver A B S hS toS hA)) :
    ∃ c : (liftOfRetraction A B S hS toS hA p x hx hp a r ha).1.right ⟶ x,
      p.IsStronglyCartesian r c ∧
        (liftOfRetraction A B S hS toS hA p x hx hp a r ha).1.hom ≫ c = 𝟙 x := by
  let : (Under.post p : Under x ⥤ Under (p.obj x)).IsFibered := underPost_isFibered p hp x
  let f : (Under.mk (eqToHom hx ≫ a) : Under (p.obj x)) ⟶ liftBaseId A B S hS toS hA p x hx :=
    Under.homMk r (by
      change (eqToHom hx ≫ a) ≫ r = eqToHom hx
      rw [Category.assoc, ha, Category.comp_id])
  exact exists_cartesian_pullbackFiber B S hS p x hp f (liftId A B S hS toS hA p x hx)

include hp in
/-- **A lift of `x` over `A[M]` pulls back along a map `f : M ⟶ N` of site modules to a lift of
`x` over `A[N]`, together with a strongly cartesian arrow over the induced morphism
`Spec A[N] ⟶ Spec A[M]` of which the structure arrows are compatible.** -/
public theorem exists_cartesian_pullback_lift {M N : SiteModule A B} (f : M ⟶ N)
    (L : LiftAlong p x (eqToHom hx ≫ squareZeroArrow A B S hS toS hA M)) :
    ∃ (L' : LiftAlong p x (eqToHom hx ≫ squareZeroArrow A B S hS toS hA N))
      (u : L'.1.right ⟶ L.1.right),
      p.IsStronglyCartesian (squareZeroOverMap A B S hS toS f) u ∧
        L'.1.hom ≫ u = L.1.hom := by
  let : (Under.post p : Under x ⥤ Under (p.obj x)).IsFibered := underPost_isFibered p hp x
  obtain ⟨u, hu, hfac⟩ := exists_cartesian_pullbackFiber B S hS p x hp
    (liftBaseThickeningMap A B S hS toS hA p x hx f) L
  exact ⟨_, u, hu, hfac⟩

end Retraction

section Canonical

variable (Λ A : Type u) [CommRing Λ] [CommRing A] [Algebra Λ A]
variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A)))
variable {X : Type v} [Category.{w} X] (p : X ⥤ BigFppfOver B S hS) (x : X)
  (hx : p.obj x = algebraOver A B S hS toS hA)
  (hp : p.IsFiberedInGroupoids) (hRS : SatisfiesRSStar B S hS p hp)
  (hΩ : B.Contains (Spec (squareZeroRing A (differentialsModule Λ A))))
  (baseMap : Spec (.of Λ) ⟶ S)
  (baseFactorization : Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ baseMap = toS)

/-- **The canonical element of `T_x(Ω_{A/Λ})` is the class of any lift of `x` over
`A[Ω_{A/Λ}]` that carries a strongly cartesian arrow back to `x` over the canonical section
`a ↦ (a, d a)` of which its structure arrow is a section.** The canonical element is defined
by one such lift, and two lifts carrying strongly cartesian arrows over one and the same
morphism of the base, compatibly with their structure arrows, are isomorphic as lifts. -/
public theorem liftEquiv_canonicalDeformationElement
    (L : LiftAlong p x (eqToHom hx ≫ squareZeroArrow A B S hS toS hA
      (differentialsSiteModule Λ A B hΩ)))
    (c : L.1.right ⟶ x)
    (hc : p.IsStronglyCartesian
      (canonicalDeformationElement Λ A B S hS toS hA p x hx hp hRS hΩ baseMap
        baseFactorization).sectionScheme c)
    (hfac : L.1.hom ≫ c = 𝟙 x) :
    (tangentFunctor A B S hS toS hA p x hx hp hRS).liftEquiv
        (differentialsSiteModule Λ A B hΩ)
        (canonicalDeformationElement Λ A B S hS toS hA p x hx hp hRS hΩ baseMap
          baseFactorization).element = Quotient.mk _ L := by
  rw [(canonicalDeformationElement Λ A B S hS toS hA p x hx hp hRS hΩ baseMap
    baseFactorization).representative_class]
  exact liftAlongClassMk_eq_of_cartesian _ L _ c
    (canonicalDeformationElement Λ A B S hS toS hA p x hx hp hRS hΩ baseMap
      baseFactorization).cartesian hc
    (((canonicalDeformationElement Λ A B S hS toS hA p x hx hp hRS hΩ baseMap
      baseFactorization).restrictsToOriginal).trans hfac.symm)

/-- A morphism of the big fppf category over `S` out of a trivial square-zero extension into
`Spec A` is the canonical section of 07YC as soon as the morphisms of schemes underlying the
two agree. -/
public theorem eq_sectionScheme_of_toScheme_map_eq
    (f : squareZeroOver A B S hS toS (differentialsSiteModule Λ A B hΩ) ⟶
      algebraOver A B S hS toS hA)
    (hf : (BigFppfOver.toScheme B S hS).map f =
      (BigFppfOver.toScheme B S hS).map
        (canonicalDeformationElement Λ A B S hS toS hA p x hx hp hRS hΩ baseMap
          baseFactorization).sectionScheme) :
    f = (canonicalDeformationElement Λ A B S hS toS hA p x hx hp hRS hΩ baseMap
      baseFactorization).sectionScheme := by
  apply Over.OverMorphism.ext
  exact ObjectProperty.hom_ext _ hf

/-- **The canonical section recovered from the data of the boundary condition.** The
comparison of trivial square-zero extensions attached to `e : M ⟶ Ω_{A/Λ}`, followed by a
morphism given by a ring map `ψ` and by a retraction given by a ring section, is the canonical
section `a ↦ (a, d a)` of 07YC as soon as the composite ring map is that section. -/
public theorem eq_sectionScheme_of_ringHom (M : SiteModule A B)
    (e : M ⟶ differentialsSiteModule Λ A B hΩ) {A₂ : Type u} [CommRing A₂]
    (hA₂ : B.Contains (Spec (.of A₂))) (toS₂ : B.obj hA₂ ⟶ B.obj hS)
    (dMap : squareZeroOver A B S hS toS M ⟶ (Over.mk toS₂ : BigFppfOver B S hS))
    (ret : (Over.mk toS₂ : BigFppfOver B S hS) ⟶ algebraOver A B S hS toS hA)
    (ψ : A₂ →+* (squareZeroRing A M.obj : Type u)) (sec : A →+* A₂)
    (hdMap : B.inclusion.map dMap.left = Spec.map (CommRingCat.ofHom ψ))
    (hret : B.inclusion.map ret.left = Spec.map (CommRingCat.ofHom sec))
    (hcomp : ∀ a : A, (squareZeroRingMap A B e).hom (ψ (sec a)) =
      (canonicalDeformationElement Λ A B S hS toS hA p x hx hp hRS hΩ baseMap
        baseFactorization).sectionRing a) :
    squareZeroOverMap A B S hS toS e ≫ dMap ≫ ret =
      (canonicalDeformationElement Λ A B S hS toS hA p x hx hp hRS hΩ baseMap
        baseFactorization).sectionScheme := by
  refine eq_sectionScheme_of_toScheme_map_eq Λ A B S hS toS hA p x hx hp hRS hΩ baseMap
    baseFactorization _ ?_
  have h1 : (BigFppfOver.toScheme B S hS).map (squareZeroOverMap A B S hS toS e) =
      Spec.map (squareZeroRingMap A B e) := rfl
  have h2 : (BigFppfOver.toScheme B S hS).map dMap = Spec.map (CommRingCat.ofHom ψ) := hdMap
  have h3 : (BigFppfOver.toScheme B S hS).map ret = Spec.map (CommRingCat.ofHom sec) := hret
  have key : (canonicalDeformationElement Λ A B S hS toS hA p x hx hp hRS hΩ baseMap
        baseFactorization).sectionRing =
      ((squareZeroRingMap A B e).hom.comp ψ).comp sec :=
    (RingHom.ext hcomp).symm
  rw [Functor.map_comp, Functor.map_comp, h1, h2, h3,
    (canonicalDeformationElement Λ A B S hS toS hA p x hx hp hRS hΩ baseMap
      baseFactorization).sectionScheme_spec, key]
  have hfold : Spec.map (squareZeroRingMap A B e) ≫ Spec.map (CommRingCat.ofHom ψ) ≫
      Spec.map (CommRingCat.ofHom sec) =
      Spec.map (CommRingCat.ofHom sec ≫ CommRingCat.ofHom ψ ≫ squareZeroRingMap A B e) := by
    rw [Spec.map_comp, Spec.map_comp, Category.assoc]
    rfl
  exact hfold

/-- **The tangent functor carries the class of a lift to the canonical element whenever the
lift pulls back to one lying over the canonical section.** Let `e : M ⟶ Ω_{A/Λ}` be a map of
site modules, `L` a lift of `x` over `A[M]` carrying a strongly cartesian arrow `c` back to
`x` over a morphism `ρ` of which its structure arrow is a section, and `L'` a lift of `x` over
`A[Ω_{A/Λ}]` carrying a strongly cartesian arrow to `L` over the map `A[M] ⟶ A[Ω_{A/Λ}]`
induced by `e`. If the composite `ρ` after that map is the canonical section `a ↦ (a, d a)`,
then the image of the class of `L` under the tangent functor is the canonical element.

The composite arrow `L' ⟶ L ⟶ x` is then strongly cartesian over the canonical section and
its structure arrow is a section of it, so the class of `L'` is the canonical element by
`Deformation.Artin.liftEquiv_canonicalDeformationElement`; and `L'` with that arrow witnesses
`L'` as the pullback of `L` along `e`, which the uniqueness of such a pullback identifies with
the value of the tangent functor. -/
public theorem functor_map_eq_canonicalDeformationElement (M : SiteModule A B)
    (e : M ⟶ differentialsSiteModule Λ A B hΩ)
    (L : LiftAlong p x (eqToHom hx ≫ squareZeroArrow A B S hS toS hA M))
    (L' : LiftAlong p x (eqToHom hx ≫ squareZeroArrow A B S hS toS hA
      (differentialsSiteModule Λ A B hΩ)))
    (u : L'.1.right ⟶ L.1.right)
    (hu : p.IsStronglyCartesian (squareZeroOverMap A B S hS toS e) u)
    (hufac : L'.1.hom ≫ u = L.1.hom)
    (ρ : squareZeroOver A B S hS toS M ⟶ algebraOver A B S hS toS hA)
    (c : L.1.right ⟶ x) (hc : p.IsStronglyCartesian ρ c) (hcfac : L.1.hom ≫ c = 𝟙 x)
    (hρ : squareZeroOverMap A B S hS toS e ≫ ρ =
      (canonicalDeformationElement Λ A B S hS toS hA p x hx hp hRS hΩ baseMap
        baseFactorization).sectionScheme) :
    (tangentFunctor A B S hS toS hA p x hx hp hRS).functor.map e
        (((tangentFunctor A B S hS toS hA p x hx hp hRS).liftEquiv M).symm
          (Quotient.mk _ L)) =
      (canonicalDeformationElement Λ A B S hS toS hA p x hx hp hRS hΩ baseMap
        baseFactorization).element := by
  have := hu
  have := hc
  have hcomp : p.IsStronglyCartesian (squareZeroOverMap A B S hS toS e ≫ ρ) (u ≫ c) :=
    inferInstance
  rw [hρ] at hcomp
  have hL' : Quotient.mk _ L' =
      (tangentFunctor A B S hS toS hA p x hx hp hRS).liftEquiv
        (differentialsSiteModule Λ A B hΩ)
        (canonicalDeformationElement Λ A B S hS toS hA p x hx hp hRS hΩ baseMap
          baseFactorization).element :=
    (liftEquiv_canonicalDeformationElement Λ A B S hS toS hA p x hx hp hRS hΩ baseMap
      baseFactorization L' (u ≫ c) hcomp (by rw [← Category.assoc, hufac, hcfac])).symm
  have hnat := (tangentFunctor A B S hS toS hA p x hx hp hRS).liftEquiv_natural e
    (((tangentFunctor A B S hS toS hA p x hx hp hRS).liftEquiv M).symm (Quotient.mk _ L))
  rw [Equiv.apply_symm_apply] at hnat
  have hpb : IsPullbackOfSquareZeroLift A B S hS toS hA p x hx e (Quotient.mk _ L)
      ((tangentFunctor A B S hS toS hA p x hx hp hRS).liftEquiv
        (differentialsSiteModule Λ A B hΩ)
        (canonicalDeformationElement Λ A B S hS toS hA p x hx hp hRS hΩ baseMap
          baseFactorization).element) :=
    ⟨L, L', rfl, hL', u, hu, hufac⟩
  exact ((tangentFunctor A B S hS toS hA p x hx hp hRS).liftEquiv
    (differentialsSiteModule Λ A B hΩ)).injective
    (isPullbackOfSquareZeroLift_unique A B S hS toS hA p x hx hp e hnat hpb)

end Canonical

/-! ### The evaluation does not see the degree-zero term of a presentation -/

section EvaluationKernel

variable {Λ A : Type u} [CommRing Λ] [CommRing A] [Algebra Λ A] {ι : Type u}

/-- **The evaluation at a square-zero thickening kills the classes coming from the degree-zero
term of a presentation.** The extension class of the thickening, read through the presentation,
factors through the projection of the two-term complex onto its conormal module, and the
inclusion of the degree-zero term followed by that projection is zero. This is why correcting
the class of clause (1) of 07YY by an element of `H¹(K ⊗ᴸ Ω_{P/Λ} ⊗_P A)`, which is what
clause (2) needs, leaves clause (1) intact. -/
public theorem obstructionEvaluation_map_twoTermInclusion
    (K : DerivedCategory (ModuleCat.{u} A)) (P : Algebra.Generators Λ A ι)
    (φ : P.Hom (canonicalGenerators Λ A)) (A' : Type u) [CommRing A'] [Algebra Λ A']
    [Algebra A' A] [IsScalarTower Λ A' A] (hq : Function.Surjective (algebraMap A' A))
    (hsq : RingHom.ker (algebraMap A' A) ^ 2 = ⊥)
    (η : (derivedTensorCohomology A K 1).obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
        (ModuleCat.of A (nlRestrict A P).X₀))) :
    letI := Stacks.Smooth.kerModule hq hsq
    obstructionEvaluation Λ A' A K hq hsq
        ((derivedTensorCohomology A K 1).map
          (DerivedCategory.Q.map (twoTermInclusion (ModuleCat.ofHom (nlRestrict A P).d)) ≫
            (derivedNaiveCotangentComplexIso Λ A P φ).hom) η) = 0 := by
  let := Stacks.Smooth.kerModule hq hsq
  have hqf : (algebraMap A' A).comp (algebraMap Λ A') = algebraMap Λ A := by
    refine RingHom.ext fun r => ?_
    exact (IsScalarTower.algebraMap_apply Λ A' A r).symm
  have hψ := presentationLift_spec P (algebraMap A' A) hq (algebraMap Λ A') hqf
  have hψΛ : ∀ r : Λ, presentationLift P (algebraMap A' A) hq (algebraMap Λ A')
      (algebraMap Λ P.toExtension.Ring r) = algebraMap Λ A' r := by
    have h : ∀ s : Λ, MvPolynomial.eval₂Hom (algebraMap Λ A')
        (fun i => (hq (P.val i)).choose) (algebraMap Λ P.Ring s) = algebraMap Λ A' s :=
      fun s => by simp
    exact h
  have hbridge := derivedNaiveCotangentComplexIso_hom_comp_cotangentExtensionClass P φ hq hsq
    (presentationLift P (algebraMap A' A) hq (algebraMap Λ A')) hψ hψΛ
    (presentationKernelMap P (algebraMap A' A) ⟨hq, hsq⟩ (algebraMap Λ A') hqf)
    (presentationKernelMap_mk P (algebraMap A' A) ⟨hq, hsq⟩ (algebraMap Λ A') hqf)
  have hcomp : (DerivedCategory.Q.map
        (twoTermInclusion (ModuleCat.ofHom (nlRestrict A P).d)) ≫
      (derivedNaiveCotangentComplexIso Λ A P φ).hom) ≫
      cotangentExtensionClass Λ A' A hq hsq = 0 := by
    rw [Category.assoc, hbridge]
    exact twoTermInclusion_comp_projection_comp _
  have hmor : (derivedTensorCohomology A K 1).map
        (DerivedCategory.Q.map (twoTermInclusion (ModuleCat.ofHom (nlRestrict A P).d)) ≫
          (derivedNaiveCotangentComplexIso Λ A P φ).hom) ≫
      obstructionEvaluation Λ A' A K hq hsq = 0 := by
    change _ ≫ ((derivedTensorCohomology A K 1).map
      (cotangentExtensionClass Λ A' A hq hsq) ≫
        (shiftedCohomologyIso A K (ModuleCat.of A (RingHom.ker (algebraMap A' A)))).hom) = 0
    rw [← Category.assoc, ← Functor.map_comp, hcomp, Functor.map_zero, Limits.zero_comp]
  rw [← ModuleCat.comp_apply, hmor]
  simp

end EvaluationKernel

/-! ### The obstruction of `C'` as the boundary of the canonical element -/

section Boundary

variable (Λ A : Type u) [CommRing Λ] [CommRing A] [Algebra Λ A]
variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) [IsLocallyNoetherian S]
variable (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A)))
variable (X : Type v) [Category.{w} X] (p : X ⥤ BigFppfOver B S hS)
variable (sit : DualDeformationSituation A Λ B S hS toS hA X p)

/-- **Under the boundary condition (iv) of 07YY, the obstruction element of `C'` is the
boundary of the canonical element of 07YC.** The condition is applied to the conormal short
exact sequence of deformation situations `(x, C̄ → A) → (x, C → A) → (x, C' → A)` and to the
lift of `x` over `C` obtained from the section of the pushout algebra. The splitting the
condition produces is that section of `C̄`, so the map `ψ : C ⟶ A[ker(C̄ → A)]` it produces
carries the section of `C` to the canonical section `a ↦ (a, d a)`; the lift over
`A[ker(C̄ → A)]` it produces therefore pulls back over the canonical section, so its tangent
class is carried to the canonical element, and the boundary identity of the condition becomes
the statement above. -/
public theorem exists_obstruction_cotangentPushoutImage_eq_boundaryMap
    (hiv : DualNotion.ObstructionBoundaryCondition Λ A B S hS toS hA X p sit) {ι : Type u}
    (P : Algebra.Generators Λ A ι) (_hE : B.Contains (Spec (.of P.toExtension.Ring)))
    (hC : B.Contains (Spec (.of (cotangentPushout P.toExtension)))) :
    letI := oppositeModule A (differentialsModule Λ A)
    letI := centralScalar A (differentialsModule Λ A)
    ∃ (hzero : (cotangentPushoutImageToPushoutHom B S hS toS hA P.toExtension hC
            sit.affineOpen sit.factorization).kernelMap ≫
          (cotangentPushoutToDifferentialsThickeningHom B S hS toS hA P.toExtension hC
            sit.finiteType sit.affineOpen sit.factorization).kernelMap = 0)
      (hSq : (ShortComplex.mk _ _ hzero).ShortExact),
      sit.obstruction (cotangentPushoutImage P.toExtension)
          (cotangentPushoutImageThickening B S hS toS hA P.toExtension
            (cotangentPushoutImage_mem_site P.toExtension B hC) sit.affineOpen
            sit.factorization) =
        boundaryMap A sit.K hSq
          ((derivedCohomology A sit.K 1).map
            (squareZeroExtKernelInv (differentialsModule Λ A))
            (sit.tangentMap
              (differentialsSiteModule Λ A B
                (differentialsSquareZero_mem_site Λ A B hA sit.finiteType))
              (canonicalDeformationElement Λ A B S hS toS hA p sit.x sit.hx sit.fibered
                  sit.rsStar (differentialsSquareZero_mem_site Λ A B hA sit.finiteType)
                  sit.affineOpen sit.factorization).element)) := by
  let := oppositeModule A (differentialsModule Λ A)
  let := centralScalar A (differentialsModule Λ A)
  set E := P.toExtension with hEdef
  set hΩ := differentialsSquareZero_mem_site Λ A B hA sit.finiteType with hΩdef
  set D₁ := differentialsBaseThickening B S hS toS hA sit.finiteType sit.affineOpen
    sit.factorization with hD₁
  set D₂ := cotangentPushoutThickening B S hS toS hA E hC sit.affineOpen sit.factorization
    with hD₂
  set D₃ := cotangentPushoutImageThickening B S hS toS hA E
    (cotangentPushoutImage_mem_site E B hC) sit.affineOpen sit.factorization with hD₃
  set g₂₁ := cotangentPushoutToDifferentialsThickeningHom B S hS toS hA E hC sit.finiteType
    sit.affineOpen sit.factorization with hg₂₁
  set g₃₂ := cotangentPushoutImageToPushoutHom B S hS toS hA E hC sit.affineOpen
    sit.factorization with hg₃₂
  -- the lift of `x` over `C` coming from the section of the pushout algebra
  set ret : (Over.mk D₂.toS' : BigFppfOver B S hS) ⟶ algebraOver A B S hS toS hA :=
    thickeningOverBaseRetraction B S hS toS hA (cotangentPushout E)
      (cotangentPushoutProj E) (isDeformationSituation_cotangentPushout E) hC
      (cotangentPushoutBaseMap E) (cotangentPushoutBaseMap_spec E) sit.affineOpen
      sit.factorization (cotangentPushoutSection E)
      (cotangentPushoutSection_comp_algebraMap E) with hret
  have hra : D₂.arrow ≫ ret = 𝟙 (algebraOver A B S hS toS hA) :=
    arrow_comp_thickeningOverBaseRetraction B S hS toS hA (cotangentPushout E)
      (cotangentPushoutProj E) (isDeformationSituation_cotangentPushout E) hC
      (cotangentPushoutBaseMap E) (cotangentPushoutBaseMap_spec E) sit.affineOpen
      sit.factorization (cotangentPushoutSection E)
      (cotangentPushoutSection_comp_algebraMap E) (cotangentPushoutProj_comp_section E)
  set lift₂ := liftOfRetraction A B S hS toS hA p sit.x sit.hx sit.fibered D₂.arrow ret hra
    with hlift₂
  obtain ⟨c₂, hc₂cart, hc₂fac⟩ :
      ∃ c : lift₂.1.right ⟶ sit.x,
        p.IsStronglyCartesian ret c ∧ lift₂.1.hom ≫ c = 𝟙 sit.x :=
    exists_cartesian_liftOfRetraction A B S hS toS hA p sit.x sit.hx sit.fibered D₂.arrow ret
      hra
  obtain ⟨hzero, hSq, hmem, s, ψ, hs, hψfst, hψsnd, hrest⟩ :=
    hiv _ _ _ D₁ D₂ D₃ g₂₁ g₃₂
      (isShortExactSequence_cotangentPushoutToDifferentialsTwisted E) lift₂
  obtain ⟨dMap, lift₁, φ, hall⟩ := hrest
  obtain ⟨hdMapSpec, harrow, hφcart, hφfac, hobs⟩ := hall
  clear harrow
  refine ⟨hzero, hSq, ?_⟩
  -- the splitting is the section of `C̄`
  have hsinl : s = TrivSqZeroExt.inlHom A (differentialsModule Λ A) :=
    eq_inlHom_of_comp_cotangentPushoutToDifferentialsTwisted E s hs
  let e : (⟨D₁.kernel, hmem⟩ : SiteModule A B) ⟶ differentialsSiteModule Λ A B hΩ :=
    ⟨(squareZeroExtKernelHom (differentialsModule Λ A) :
      D₁.kernel ⟶ differentialsModule Λ A)⟩
  -- the composite ring map is the canonical section
  have hcomp : ∀ a : A, (squareZeroRingMap A B e).hom (ψ (cotangentPushoutSection E a)) =
      (canonicalDeformationElement Λ A B S hS toS hA p sit.x sit.hx sit.fibered sit.rsStar hΩ
        sit.affineOpen sit.factorization).sectionRing a := by
    intro a
    have h3 : D₂.q (cotangentPushoutSection E a) = a := TrivSqZeroExt.fst_inl A a
    have h2 : g₂₁.ringHom (cotangentPushoutSection E a) =
        TrivSqZeroExt.inl a + TrivSqZeroExt.inr (KaehlerDifferential.D Λ A a) :=
      cotangentPushoutToDifferentialsTwisted_section E a
    have hker : ((ψ (cotangentPushoutSection E a)).snd).1 =
        TrivSqZeroExt.inr (KaehlerDifferential.D Λ A a) := by
      rw [hψsnd, hsinl, h2, h3]
      change TrivSqZeroExt.inl a + TrivSqZeroExt.inr (KaehlerDifferential.D Λ A a) -
        TrivSqZeroExt.inl a = _
      abel
    rw [(canonicalDeformationElement Λ A B S hS toS hA p sit.x sit.hx sit.fibered sit.rsStar hΩ
      sit.affineOpen sit.factorization).sectionRing_apply]
    refine TrivSqZeroExt.ext ?_ ?_
    · refine (fst_squareZeroExtMap (squareZeroExtKernelHom (differentialsModule Λ A))
        (ψ (cotangentPushoutSection E a))).trans ?_
      exact (hψfst (cotangentPushoutSection E a)).trans h3
    · refine (snd_squareZeroExtMap (squareZeroExtKernelHom (differentialsModule Λ A))
        (ψ (cotangentPushoutSection E a))).trans ?_
      change ((ψ (cotangentPushoutSection E a)).snd).1.snd = KaehlerDifferential.D Λ A a
      rw [hker, TrivSqZeroExt.snd_inr]
  have hρ : squareZeroOverMap A B S hS toS e ≫ dMap ≫ ret =
      (canonicalDeformationElement Λ A B S hS toS hA p sit.x sit.hx sit.fibered sit.rsStar hΩ
        sit.affineOpen sit.factorization).sectionScheme :=
    eq_sectionScheme_of_ringHom Λ A B S hS toS hA p sit.x sit.hx sit.fibered sit.rsStar hΩ
      sit.affineOpen sit.factorization (⟨D₁.kernel, hmem⟩ : SiteModule A B) e D₂.hA' D₂.toS'
      dMap ret ψ (cotangentPushoutSection E) hdMapSpec rfl hcomp
  -- the lift over `A[ker(C̄ → A)]` has the canonical element as its class
  obtain ⟨L', u, hucart, hufac⟩ := exists_cartesian_pullback_lift A B S hS toS hA p sit.x
    sit.hx sit.fibered e lift₁
  have hcart : p.IsStronglyCartesian (dMap ≫ ret) (φ ≫ c₂) := by
    have := hφcart
    have := hc₂cart
    infer_instance
  have hfac : lift₁.1.hom ≫ φ ≫ c₂ = 𝟙 sit.x := by
    rw [← Category.assoc, hφfac, hc₂fac]
  have hcanon := functor_map_eq_canonicalDeformationElement Λ A B S hS toS hA p sit.x sit.hx
    sit.fibered sit.rsStar hΩ sit.affineOpen sit.factorization
    (⟨D₁.kernel, hmem⟩ : SiteModule A B) e lift₁ L' u hucart hufac (dMap ≫ ret) (φ ≫ c₂)
    hcart hfac hρ
  -- transport the tangent class along `e`
  have hnat := sit.tangentNatural e
    (((tangentFunctor A B S hS toS hA p sit.x sit.hx sit.fibered sit.rsStar).liftEquiv
      (⟨D₁.kernel, hmem⟩ : SiteModule A B)).symm (Quotient.mk _ lift₁))
  rw [hcanon] at hnat
  have he2 : e.hom ≫ squareZeroExtKernelInv (differentialsModule Λ A) = 𝟙 D₁.kernel :=
    squareZeroExtKernelHom_comp_inv (differentialsModule Λ A)
  rw [hobs]
  congr 1
  have hone : ∀ z : ((derivedCohomology A sit.K 1).obj D₁.kernel),
      (derivedCohomology A sit.K 1).map (𝟙 D₁.kernel) z = z := by
    intro z
    rw [show (derivedCohomology A sit.K 1).map (𝟙 D₁.kernel) = 𝟙 _ from by simp]
    rfl
  rw [hnat, ← ModuleCat.comp_apply, ← Functor.map_comp, he2]
  exact (hone _).symm

/-- The image in the derived category of a module map placed in degree zero. -/
private theorem Q_map_single_map {A' : Type u} [CommRing A'] {M N : ModuleCat.{u} A'}
    (f : M ⟶ N) :
    DerivedCategory.Q.map
        ((HomologicalComplex.single (ModuleCat.{u} A') (ComplexShape.up ℤ) 0).map f) =
      (DerivedCategory.singleFunctor (ModuleCat.{u} A') 0).map f :=
  rfl

/-- A retraction of modules is a retraction on the cohomology of the derived tensor
product. -/
private theorem map_single_comp_apply (A : Type u) [CommRing A]
    (K : DerivedCategory (ModuleCat.{u} A)) {M N : ModuleCat.{u} A} (f : M ⟶ N) (g : N ⟶ M)
    (hfg : f ≫ g = 𝟙 M)
    (v : (derivedTensorCohomology A K 1).obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)) :
    (derivedTensorCohomology A K 1).map
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map g)
        ((derivedTensorCohomology A K 1).map
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map f) v) = v := by
  rw [← ModuleCat.comp_apply, ← CategoryTheory.Functor.map_comp,
    ← CategoryTheory.Functor.map_comp, hfg, CategoryTheory.Functor.map_id,
    CategoryTheory.Functor.map_id, ModuleCat.id_apply]

/-- **Two classes with the same boundary differ by one coming from the middle term.** Read
through a map `ker` out of the third term of the sequence and a factorization
`Sq.g ≫ ker = t ≫ u` of the induced map, the difference of their images under `ker` is the
image under `u` of a class on `N`. -/
private theorem exists_map_eq_sub_of_boundaryMap_eq (A : Type u) [CommRing A]
    (K : DerivedCategory (ModuleCat.{u} A)) {Sq : ShortComplex (ModuleCat.{u} A)}
    (hSq : Sq.ShortExact) {M N : ModuleCat.{u} A} (ker : Sq.X₃ ⟶ M) (t : Sq.X₂ ⟶ N)
    (u : N ⟶ M) (htu : Sq.g ≫ ker = t ≫ u)
    (z₁ z₂ : (derivedTensorCohomology A K 1).obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj Sq.X₃))
    (h : boundaryMap A K hSq z₁ = boundaryMap A K hSq z₂)
    (v₁ v₂ : (derivedTensorCohomology A K 1).obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M))
    (hv₁ : (derivedTensorCohomology A K 1).map
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map ker) z₁ = v₁)
    (hv₂ : (derivedTensorCohomology A K 1).map
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map ker) z₂ = v₂) :
    ∃ y : (derivedTensorCohomology A K 1).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N),
      (derivedTensorCohomology A K 1).map
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map u) y = v₁ - v₂ := by
  obtain ⟨y₀, hy₀⟩ := exists_of_boundaryMap_eq_zero A K hSq (z₁ - z₂)
    (by rw [map_sub, h, sub_self])
  have hy : (derivedTensorCohomology A K 1).map
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map Sq.g) y₀ = z₁ - z₂ := hy₀
  have hcomp : (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map Sq.g ≫
      (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map ker =
      (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map t ≫
        (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map u := by
    rw [← CategoryTheory.Functor.map_comp, htu, CategoryTheory.Functor.map_comp]
  refine ⟨(derivedTensorCohomology A K 1).map
    ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map t) y₀, ?_⟩
  rw [← ModuleCat.comp_apply, ← CategoryTheory.Functor.map_comp, ← hcomp,
    CategoryTheory.Functor.map_comp, ModuleCat.comp_apply, hy, map_sub, hv₁, hv₂]

/-- **The correction of the class of clause (1) that makes clause (2) hold.** Under the
boundary condition (iv), the class produced at a presentation `P` by clause (1) differs from
the canonical element, after projection to `H¹(K ⊗ᴸ Ω_{A/Λ})`, by the image of a class on the
degree-zero term `Ω_{P/Λ} ⊗_P A` of `NL(α)`: condition (iv) makes the obstruction of `C'` the
boundary of the canonical element, clause (1) makes it the boundary of the image of the class
under the projection of `NL(α)` onto `ker(C̄ → A)[0]`, and the long exact sequence of the
conormal kernel sequence identifies the difference with a class on `ker(C → A)`. Correcting
the class by that image is invisible to clause (1) and makes clause (2) hold, which is the
conclusion stated here. -/
private theorem exists_correction_of_boundaryCondition
    (hiv : DualNotion.ObstructionBoundaryCondition Λ A B S hS toS hA X p sit)
    {ι : Type u} [Finite ι]
    (P : Algebra.Generators Λ A ι) (hE : B.Contains (Spec (.of P.Ring)))
    (hC : B.Contains (Spec (.of (cotangentPushout P.toExtension))))
    (ξ₀ : (derivedTensorCohomology A sit.K 1).obj
      (DerivedCategory.Q.obj (twoTermComplex (nlRestrict A P))))
    (hξ₀ : ∀ (A' : Type u) [CommRing A'] (D : SquareZeroThickening A B S hS toS hA A')
      (f : Λ →+* A')
      (_hfS : Spec.map (CommRingCat.ofHom f) ≫ sit.affineOpen = B.inclusion.map D.toS')
      (hf : D.q.comp f = algebraMap Λ A),
      letI : Algebra Λ A' := f.toAlgebra
      letI : Algebra A' A := D.q.toAlgebra
      letI : IsScalarTower Λ A' A :=
        IsScalarTower.of_algebraMap_eq fun r =>
          (congrArg (fun g : Λ →+* A => g r) hf).symm
      obstructionEvaluation Λ A' A sit.K D.squareZeroSurjection.1
          D.squareZeroSurjection.2
          ((derivedTensorCohomology A sit.K 1).map
            (derivedNaiveCotangentComplexIso Λ A P
              (P.defaultHom (canonicalGenerators Λ A))).hom ξ₀) =
        sit.obstruction A' D) :
    ∃ η : (derivedTensorCohomology A sit.K 1).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
          (ModuleCat.of A (nlRestrict A P).X₀)),
      sit.tangentMap
          (differentialsSiteModule Λ A B
            (differentialsSquareZero_mem_site Λ A B hA sit.finiteType))
          (canonicalDeformationElement Λ A B S hS toS hA p sit.x sit.hx sit.fibered sit.rsStar
            (differentialsSquareZero_mem_site Λ A B hA sit.finiteType) sit.affineOpen
            sit.factorization).element =
        (derivedTensorCohomology A sit.K 1).map (naiveCotangentToDifferentials Λ A)
          ((derivedTensorCohomology A sit.K 1).map
              (derivedNaiveCotangentComplexIso Λ A P
                (P.defaultHom (canonicalGenerators Λ A))).hom ξ₀ -
            (derivedTensorCohomology A sit.K 1).map
              (DerivedCategory.Q.map (twoTermInclusion (ModuleCat.ofHom (nlRestrict A P).d)) ≫
                (derivedNaiveCotangentComplexIso Λ A P
                  (P.defaultHom (canonicalGenerators Λ A))).hom) η) := by
  obtain ⟨a, b, hab, w, hdw, hwg, hkval, proj, ker, hproj, -, hkerproj, hkerg, hinvker⟩ :=
    exists_conormalKernelComparison B S hS toS hA sit.affineOpen sit.factorization P
      (P.defaultHom (canonicalGenerators Λ A)) hE hC sit.finiteType
  obtain ⟨hzero, hSq, hbd⟩ := exists_obstruction_cotangentPushoutImage_eq_boundaryMap Λ A B S hS
    toS hA X p sit hiv P hE hC
  -- the extension class of `C' → A`, read on the two-term complex of the presentation
  let : Algebra Λ (cotangentPushoutImage P.toExtension) :=
    (cotangentPushoutImageBaseMap P.toExtension).toAlgebra
  let : Algebra (cotangentPushoutImage P.toExtension) A :=
    (cotangentPushoutImageProj P.toExtension).toAlgebra
  have hqf : (cotangentPushoutImageProj P.toExtension).comp
      (cotangentPushoutImageBaseMap P.toExtension) = algebraMap Λ A :=
    cotangentPushoutImageBaseMap_spec P.toExtension
  let : IsScalarTower Λ (cotangentPushoutImage P.toExtension) A :=
    IsScalarTower.of_algebraMap_eq fun r => (congrArg (fun g : Λ →+* A => g r) hqf).symm
  have hq : Function.Surjective (algebraMap (cotangentPushoutImage P.toExtension) A) :=
    (isDeformationSituation_cotangentPushoutImage P.toExtension).1
  have hsq : RingHom.ker (algebraMap (cotangentPushoutImage P.toExtension) A) ^ 2 = ⊥ :=
    (isDeformationSituation_cotangentPushoutImage P.toExtension).2
  have hψ : ∀ x, algebraMap (cotangentPushoutImage P.toExtension) A
      (((cotangentPushoutInfinitesimalMap P.toExtension).rangeRestrict.comp
        (Ideal.Quotient.mk (P.toExtension.ker ^ 2))) x) =
      algebraMap P.toExtension.Ring A x := fun x => cotangentPushoutFun_fst P.toExtension x
  have hψΛ : ∀ r : Λ, ((cotangentPushoutInfinitesimalMap P.toExtension).rangeRestrict.comp
      (Ideal.Quotient.mk (P.toExtension.ker ^ 2))) (algebraMap Λ P.toExtension.Ring r) =
      algebraMap Λ (cotangentPushoutImage P.toExtension) r := fun _ => rfl
  have hcls := derivedNaiveCotangentComplexIso_hom_comp_cotangentExtensionClass P
    (P.defaultHom (canonicalGenerators Λ A)) hq hsq
    ((cotangentPushoutInfinitesimalMap P.toExtension).rangeRestrict.comp
      (Ideal.Quotient.mk (P.toExtension.ker ^ 2))) hψ hψΛ a.hom
    fun x => Subtype.ext (hkval x)
  have hfS : Spec.map (CommRingCat.ofHom (cotangentPushoutImageBaseMap P.toExtension)) ≫
      sit.affineOpen =
      B.inclusion.map (cotangentPushoutImageThickening B S hS toS hA P.toExtension
        (cotangentPushoutImage_mem_site P.toExtension B hC) sit.affineOpen
        sit.factorization).toS' := rfl
  have hobs := hξ₀ (cotangentPushoutImage P.toExtension)
    (cotangentPushoutImageThickening B S hS toS hA P.toExtension
      (cotangentPushoutImage_mem_site P.toExtension B hC) sit.affineOpen sit.factorization)
    (cotangentPushoutImageBaseMap P.toExtension) hfS hqf
  have hbdy := shiftedCohomologyIso_map_eq_boundaryMap sit.K hSq a b hab w hwg hdw
    (derivedNaiveCotangentComplexIso Λ A P (P.defaultHom (canonicalGenerators Λ A)))
    (cotangentExtensionClass Λ (cotangentPushoutImage P.toExtension) A hq hsq) hcls proj hproj
    ((derivedTensorCohomology A sit.K 1).map
      (derivedNaiveCotangentComplexIso Λ A P
        (P.defaultHom (canonicalGenerators Λ A))).hom ξ₀)
  -- the obstruction of `C'` is the boundary of a class carried to the canonical element
  obtain ⟨z, hz, hzcan⟩ : ∃ z, sit.obstruction (cotangentPushoutImage P.toExtension)
        (cotangentPushoutImageThickening B S hS toS hA P.toExtension
          (cotangentPushoutImage_mem_site P.toExtension B hC) sit.affineOpen
          sit.factorization) = boundaryMap A sit.K hSq z ∧
      (derivedTensorCohomology A sit.K 1).map
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map ker) z =
        sit.tangentMap (differentialsSiteModule Λ A B
            (differentialsSquareZero_mem_site Λ A B hA sit.finiteType))
          (canonicalDeformationElement Λ A B S hS toS hA p sit.x sit.hx sit.fibered sit.rsStar
            (differentialsSquareZero_mem_site Λ A B hA sit.finiteType) sit.affineOpen
            sit.factorization).element := by
    refine ⟨_, hbd, ?_⟩
    exact map_single_comp_apply A sit.K _ ker hinvker _
  have hboth : boundaryMap A sit.K hSq ((derivedTensorCohomology A sit.K 1).map proj
        ((derivedTensorCohomology A sit.K 1).map
          (derivedNaiveCotangentComplexIso Λ A P
            (P.defaultHom (canonicalGenerators Λ A))).hom ξ₀)) =
      boundaryMap A sit.K hSq z := (hobs.symm.trans hbdy).symm.trans hz
  have hprojker : (derivedTensorCohomology A sit.K 1).map
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map ker)
        ((derivedTensorCohomology A sit.K 1).map proj
          ((derivedTensorCohomology A sit.K 1).map
            (derivedNaiveCotangentComplexIso Λ A P
              (P.defaultHom (canonicalGenerators Λ A))).hom ξ₀)) =
      (derivedTensorCohomology A sit.K 1).map (naiveCotangentToDifferentials Λ A)
        ((derivedTensorCohomology A sit.K 1).map
          (derivedNaiveCotangentComplexIso Λ A P
            (P.defaultHom (canonicalGenerators Λ A))).hom ξ₀) := by
    rw [← ModuleCat.comp_apply, ← CategoryTheory.Functor.map_comp, hkerproj]
  obtain ⟨η, hη⟩ := exists_map_eq_sub_of_boundaryMap_eq A sit.K hSq ker _ _ hkerg _ _ hboth
    _ _ hprojker hzcan
  refine ⟨η, ?_⟩
  have hcorr : (derivedTensorCohomology A sit.K 1).map (naiveCotangentToDifferentials Λ A)
        ((derivedTensorCohomology A sit.K 1).map
          (DerivedCategory.Q.map (twoTermInclusion (ModuleCat.ofHom (nlRestrict A P).d)) ≫
            (derivedNaiveCotangentComplexIso Λ A P
              (P.defaultHom (canonicalGenerators Λ A))).hom) η) =
      (derivedTensorCohomology A sit.K 1).map
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map
          (ModuleCat.ofHom P.toExtension.toKaehler)) η := by
    rw [← ModuleCat.comp_apply, ← CategoryTheory.Functor.map_comp, Category.assoc,
      derivedNaiveCotangentComplexIso_hom_comp_naiveCotangentToDifferentials,
      ← CategoryTheory.Functor.map_comp, presentationToDifferentials_eq P,
      twoTermInclusion_comp_twoTermToSingle, Q_map_single_map]
  rw [map_sub, hcorr, hη, sub_sub_cancel]

/-- **Correcting a class by one coming from the degree-zero term of a presentation does not
change its evaluation at square-zero thickenings.** The extension class of the thickening,
read through the presentation, factors through the projection of the two-term complex onto its
conormal module, and the inclusion of the degree-zero term followed by that projection is
zero. -/
private theorem obstructionEvaluation_sub_twoTermInclusion {ι : Type u}
    (P : Algebra.Generators Λ A ι)
    (ξ : (derivedTensorCohomology A sit.K 1).obj (derivedNaiveCotangentComplex Λ A))
    (η : (derivedTensorCohomology A sit.K 1).obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
        (ModuleCat.of A (nlRestrict A P).X₀)))
    (A' : Type u) [CommRing A'] (D : SquareZeroThickening A B S hS toS hA A') (f : Λ →+* A')
    (hf : D.q.comp f = algebraMap Λ A) :
    letI : Algebra Λ A' := f.toAlgebra
    letI : Algebra A' A := D.q.toAlgebra
    letI : IsScalarTower Λ A' A :=
      IsScalarTower.of_algebraMap_eq fun r =>
        (congrArg (fun g : Λ →+* A => g r) hf).symm
    obstructionEvaluation Λ A' A sit.K D.squareZeroSurjection.1 D.squareZeroSurjection.2
        (ξ - (derivedTensorCohomology A sit.K 1).map
          (DerivedCategory.Q.map (twoTermInclusion (ModuleCat.ofHom (nlRestrict A P).d)) ≫
            (derivedNaiveCotangentComplexIso Λ A P
              (P.defaultHom (canonicalGenerators Λ A))).hom) η) =
      obstructionEvaluation Λ A' A sit.K D.squareZeroSurjection.1
        D.squareZeroSurjection.2 ξ := by
  let : Algebra Λ A' := f.toAlgebra
  let : Algebra A' A := D.q.toAlgebra
  let : IsScalarTower Λ A' A :=
    IsScalarTower.of_algebraMap_eq fun r =>
      (congrArg (fun g : Λ →+* A => g r) hf).symm
  rw [map_sub, obstructionEvaluation_map_twoTermInclusion sit.K P
    (P.defaultHom (canonicalGenerators Λ A)) A' D.squareZeroSurjection.1
    D.squareZeroSurjection.2 η, sub_zero]

/-- **Stacks 07YY.** A dual deformation situation satisfying the boundary condition (iv) has a
cotangent obstruction class: a single class `ξ` on `NL_{A/Λ}` whose evaluation at every
square-zero thickening is that thickening's obstruction element, and whose image in
`H¹(K ⊗ᴸ Ω_{A/Λ})` is the canonical element of the tangent functor.

The class of clause (1), built at a chosen presentation, need not satisfy clause (2); it is
corrected by an element of `H¹(K ⊗ᴸ Ω_{P/Λ} ⊗_P A)` supplied by
`Deformation.Artin.exists_correction_of_boundaryCondition`, and the correction is invisible to
clause (1) because the inclusion of the degree-zero term of `NL(α)` followed by the projection
onto the conormal module is zero. -/
@[stacks 07YY]
public theorem exists_isCotangentObstructionClass
    (hiv : DualNotion.ObstructionBoundaryCondition Λ A B S hS toS hA X p sit) :
    ∃ ξ, IsCotangentObstructionClass Λ A B S hS toS hA X p sit ξ := by
  obtain ⟨ι, hfin, ⟨P⟩⟩ := exists_finite_generators (Λ := Λ) (A := A) sit.finiteType
  have : Finite ι := hfin
  have hΛ : B.Contains (Spec (.of Λ)) :=
    contains_of_isOpenImmersion B sit.affineOpen sit.openImmersion hS
  have hE : B.Contains (Spec (.of P.Ring)) := presentation_mem_site_of_finite P B hΛ
  have hC : B.Contains (Spec (.of (cotangentPushout P.toExtension))) :=
    cotangentPushout_mem_site_of_finite P B hA
  obtain ⟨ξ₀, hξ₀⟩ := exists_obstructionEvaluation_eq_obstruction_of_presentation Λ A B S hS
    toS hA X p sit P hE hC
  obtain ⟨η, hη⟩ := exists_correction_of_boundaryCondition Λ A B S hS toS hA X p sit hiv P hE
    hC ξ₀ hξ₀
  refine ⟨_, ?_, hη⟩
  intro A' _ D
  obtain ⟨f, hfS, hqf⟩ := exists_baseRingHom B S hS toS hA D sit.affineOpen
    sit.openImmersion sit.factorization
  refine ⟨f, hfS, hqf, ?_⟩
  exact (obstructionEvaluation_sub_twoTermInclusion Λ A B S hS toS hA X p sit P _ η A' D f
    hqf).trans (hξ₀ A' D f hfS hqf)
end Boundary

end Deformation.Artin

end
