module

public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GaloisCompactSupportResolutionGalois
public import StacksFrontier.AlgebraicGeometry.ContinuousCohomology.InternalHomPairingPerfect
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationSheafExact
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyZero
public import StacksFrontier.AlgebraicGeometry.ContinuousCohomology.FiniteTypeDual

/-!
# The family of Poincaré pairings and its perfectness

For a finite module `M` with continuous `π₁(X)`-action and an injective resolution `I` of `j_! ℱ_M`
on the compactification (supported in degrees `≥ 0`), the Galois evaluation pairing followed by a
trace `t : Γ^Gal(K) ⟶ T` (`K` a resolution of `j_! μ_n`, `T` the injective resolution of `ℚ/ℤ[-2]`)
gives a chain map `Γ^Gal(I) ⟶ Hom^•_ℤ(Γ^Gal(ℋom^•(I, K)), T)`. This file shows that it is a
quasi-isomorphism for all `(M, I)` at once, given the base case in degree `2`, the vanishing of the
cohomology of `Γ^Gal(ℋom^•(I, K))` outside `[0, 2]`, and coeffacements of the cohomological side.

## Main definitions

* `AlgebraicGeometry.PoincareIndex`: a finite module `M` with continuous `π₁(X)`-action together
  with an injective resolution of `j_! ℱ_M` supported in degrees `≥ 0`.
* `AlgebraicGeometry.poincarePairing`: the evaluation pairing of a member of the family followed
  by the trace.

## Main results

* `AlgebraicGeometry.exists_poincareCoeffacingEpi`: coeffacing epimorphisms for the family.
* `AlgebraicGeometry.poincarePairing_step`: a coeffacing epimorphism gives short exact sequences of
  chain models compatible with the pairings.
* `AlgebraicGeometry.quasiIso_poincarePairing`: the Poincaré pairings of the family are
  quasi-isomorphisms.

## References

* [Stacks Project, Tag 03VM](https://stacks.math.columbia.edu/tag/03VM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Frobenius
open Stacks.GroupCohomology Stacks.EtaleCohomology

universe u

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

/-- Étale sheaves of modules over a ring `Λ : Type` have enough injectives. -/
local instance (priority := 3000) etaleModules_enoughInjectives_poincareFamily (Λ : Type)
    [Ring Λ] (Y : Scheme.{u}) : EnoughInjectives (EtaleModules.{u, 0} Λ Y) :=
  etaleModules_enoughInjectives.{u, 0} Λ Y

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1]
  (x : GeometricPoint X.1) (Λ : Type) [Ring Λ] [Finite Λ]
  {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k)) [IsCurve k f] [Smooth f]
  [GeometricallyConnected f] (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar]
  [Algebra k kbar] [IsAlgClosed kbar] [Algebra.IsSeparable k kbar]
  [CompactSpace (kbar ≃ₐ[k] kbar)]

/-- The members of the family: a finite module `M` with continuous `π₁(X)`-action and an
injective resolution of `j_! ℱ_M` on the compactification, supported in degrees `≥ 0`. -/
structure PoincareIndex where
  /-- The module. -/
  M : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x)
  /-- The resolution of `j_! ℱ_M`. -/
  I : CochainComplex.InjectiveResolution
    ((CochainComplex.singleFunctor (EtaleModules.{u, 0} Λ (Over.mk j.toBase).left) 0).obj
      ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj ((representationSheaf B X x Λ).obj M)))
  /-- The resolution is supported in degrees `≥ 0`. -/
  ge : I.cocomplex.IsStrictlyGE 0

variable {B X x Λ f j}

variable (Kc : CochainComplex (EtaleModules.{u, 0} ℤ (Over.mk j.toBase).left) ℤ)
  (t : galoisHomOpG (Over.mk j.toBase) kbar Kc ⟶
    Stacks.ContinuousCohomology.traceTarget.{u, u + 1} (kbar ≃ₐ[k] kbar) 2)

/-- The Poincaré pairing of a member of the family: evaluation followed by the trace. -/
def poincarePairing (i : PoincareIndex B X x Λ f j) :
    Stacks.ContinuousCohomology.ComplexPairing Λᵐᵒᵖ (RingEquiv.opOp Λ).toRingHom
      (galoisHomOpA (Over.mk j.toBase) kbar i.I.cocomplex)
      (galoisHomOpE (Over.mk j.toBase) kbar i.I.cocomplex Kc)
      (Stacks.ContinuousCohomology.traceTarget.{u, u + 1} (kbar ≃ₐ[k] kbar) 2) :=
  (galoisHomOpComplexPairing (Over.mk j.toBase) kbar i.I.cocomplex Kc).postcomp t

omit [IsCurve k f] [Smooth f] [GeometricallyConnected f] [IsAlgClosed kbar]
  [CompactSpace (kbar ≃ₐ[k] kbar)] in
/-- The chain model `Γ^Gal(I)` has no cohomology in negative degrees. -/
lemma isZero_homology_galoisHomOpA_of_neg (i : PoincareIndex B X x Λ f j) (m : ℤ) (hm : m < 0) :
    IsZero ((galoisHomOpA (Over.mk j.toBase) kbar i.I.cocomplex).homology m) := by
  have := i.ge
  exact ShortComplex.isZero_homology_of_isZero_X₂ _
    ((galoisGlobalSections Λ (Over.mk j.toBase) kbar).map_isZero
      (CochainComplex.isZero_of_isStrictlyGE i.I.cocomplex 0 m hm))

/-- The resolution of `j_! ℱ_N` from a resolving complex, as a member of the family. -/
def PoincareIndex.mk'
    (N : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x))
    (T : CochainComplex (EtaleModules.{u, 0} Λ (Over.mk j.toBase).left) ℤ) [T.IsStrictlyGE 0]
    [∀ q, Injective (T.X q)]
    (ι : (HomologicalComplex.single (EtaleModules.{u, 0} Λ (Over.mk j.toBase).left)
        (ComplexShape.up ℤ) 0).obj
      ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj
        ((representationSheaf B X x Λ).obj N)) ⟶ T)
    [QuasiIso ι] : PoincareIndex B X x Λ f j where
  M := N
  I := { cocomplex := T, boundedBelow := ⟨0, inferInstance⟩, ι := ι }
  ge := inferInstance

omit [IsCurve k f] [Smooth f] [GeometricallyConnected f] [IsAlgClosed kbar]
  [CompactSpace (kbar ≃ₐ[k] kbar)] in
/-- The Poincaré pairings are compatible with a morphism of resolutions. -/
lemma poincarePairing_precomp (i i' : PoincareIndex B X x Λ f j)
    (φ : i'.I.cocomplex ⟶ i.I.cocomplex) (n p q : ℤ) (h : p + n = q)
    (a : ((galoisHomOpA (Over.mk j.toBase) kbar i'.I.cocomplex).X n).obj.obj.V)
    (e : ((galoisHomOpE (Over.mk j.toBase) kbar i.I.cocomplex Kc).X p).obj.obj.V) :
    (poincarePairing kbar Kc t i).pair n p q h
        ((((galoisGlobalSections Λ (Over.mk j.toBase) kbar).mapHomologicalComplex _).map φ).f n
          |>.hom.hom.hom.hom a)
        e =
      (poincarePairing kbar Kc t i').pair n p q h a
        ((((galoisGlobalSections Λᵐᵒᵖ (Over.mk j.toBase) kbar).mapHomologicalComplex _).map
          (Stacks.AbelianInternalHom.homOpComplexPrecomp
            (M := etaleHomOpTarget (Over.mk j.toBase) Kc) φ)).f p
            |>.hom.hom.hom.hom e) :=
  congrArg (t.f q).hom.hom.hom.hom
    (galoisHomOpPair_precomp (Over.mk j.toBase) kbar Kc φ n p q h a e)

omit [ConnectedSpace X.1] [Finite Λ] [IsCurve k f] [Smooth f] [GeometricallyConnected f]
  [IsAlgClosed kbar] [CompactSpace (kbar ≃ₐ[k] kbar)] in
/-- `Γ^Gal` carries a zero composite of complexes to a zero composite. -/
lemma galoisHomOpA_map_comp_eq_zero
    {L₁ L₂ L₃ : CochainComplex (EtaleModules.{u, 0} Λ (Over.mk j.toBase).left) ℤ}
    (f₁ : L₁ ⟶ L₂) (f₂ : L₂ ⟶ L₃) (w : f₁ ≫ f₂ = 0) :
    ((galoisGlobalSections Λ (Over.mk j.toBase) kbar).mapHomologicalComplex
        (ComplexShape.up ℤ)).map f₁ ≫
      ((galoisGlobalSections Λ (Over.mk j.toBase) kbar).mapHomologicalComplex
        (ComplexShape.up ℤ)).map f₂ = 0 := by
  rw [← Functor.map_comp, w, Functor.map_zero]

omit [ConnectedSpace X.1] [Finite Λ] [IsCurve k f] [Smooth f] [GeometricallyConnected f]
  [IsAlgClosed kbar] [CompactSpace (kbar ≃ₐ[k] kbar)] in
/-- `Γ^Gal(ℋom^•(-, K))` carries a zero composite of complexes to a zero composite. -/
lemma galoisHomOpE_map_comp_eq_zero
    {L₁ L₂ L₃ : CochainComplex (EtaleModules.{u, 0} Λ (Over.mk j.toBase).left) ℤ}
    (f₁ : L₁ ⟶ L₂) (f₂ : L₂ ⟶ L₃) (w : f₁ ≫ f₂ = 0) :
    ((galoisGlobalSections Λᵐᵒᵖ (Over.mk j.toBase) kbar).mapHomologicalComplex
        (ComplexShape.up ℤ)).map
        (Stacks.AbelianInternalHom.homOpComplexPrecomp
          (M := etaleHomOpTarget (Over.mk j.toBase) Kc) f₂) ≫
      ((galoisGlobalSections Λᵐᵒᵖ (Over.mk j.toBase) kbar).mapHomologicalComplex
        (ComplexShape.up ℤ)).map
        (Stacks.AbelianInternalHom.homOpComplexPrecomp
          (M := etaleHomOpTarget (Over.mk j.toBase) Kc) f₁) = 0 :=
  by
  rw [← Functor.map_comp, Stacks.AbelianInternalHom.homOpComplexPrecomp_comp, w,
    Stacks.AbelianInternalHom.homOpComplexPrecomp_zero, Functor.map_zero]

omit [CompactSpace (kbar ≃ₐ[k] kbar)] in
/-- **Coeffacing epimorphisms for the family**: for `m < 2`, an epimorphism `π : P ⟶ M` that is
zero on `H^m(Γ^Gal(-))` and on `H^{2-m}(Γ^Gal(ℋom^•(-, K)))` for all lifts to resolutions. -/
lemma exists_poincareCoeffacingEpi
    (hcoeff : (compactSupportRepresentationHomology B X x Λ f j kbar).Coeffaceable)
    (hE : ∀ (i : PoincareIndex B X x Λ f j) (q : ℤ), (q < 0 ∨ 2 < q) →
      IsZero ((galoisHomOpE (Over.mk j.toBase) kbar i.I.cocomplex Kc).homology q))
    (hD : ∀ (n : ℕ), 1 ≤ n → n ≤ 2 →
      ∀ N : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x),
      ∃ (N' : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x))
        (π' : N' ⟶ N), Epi π' ∧
      ∀ (M : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x))
        (π : N ⟶ M)
        (IM : CochainComplex.InjectiveResolution
          ((CochainComplex.singleFunctor (EtaleModules.{u, 0} Λ (Over.mk j.toBase).left) 0).obj
            ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj
              ((representationSheaf B X x Λ).obj M))))
        (IN : CochainComplex.InjectiveResolution
          ((CochainComplex.singleFunctor (EtaleModules.{u, 0} Λ (Over.mk j.toBase).left) 0).obj
            ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj
              ((representationSheaf B X x Λ).obj N'))))
        (φ : IN.cocomplex ⟶ IM.cocomplex)
        (_ : (IN.ι ≫ φ = (CochainComplex.singleFunctor _ 0).map
          ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).map
            ((representationSheaf B X x Λ).map (π' ≫ π))) ≫ IM.ι)),
        HomologicalComplex.homologyMap
          (((galoisGlobalSections Λᵐᵒᵖ (Over.mk j.toBase) kbar).mapHomologicalComplex _).map
            (Stacks.AbelianInternalHom.homOpComplexPrecomp
              (M := etaleHomOpTarget (Over.mk j.toBase) Kc) φ)) (n : ℤ) = 0)
    (i : PoincareIndex B X x Λ f j) (m : ℤ) (hm : m < 2) :
    ∃ (P : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x))
      (π : P ⟶ i.M), Epi π ∧
      (∀ (IP : CochainComplex.InjectiveResolution
          ((CochainComplex.singleFunctor (EtaleModules.{u, 0} Λ (Over.mk j.toBase).left) 0).obj
            ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj
              ((representationSheaf B X x Λ).obj P))))
        [IP.cocomplex.IsStrictlyGE 0]
        (φ : IP.cocomplex ⟶ i.I.cocomplex) (_ : (IP.ι ≫ φ = (CochainComplex.singleFunctor _ 0).map
          ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).map
            ((representationSheaf B X x Λ).map π)) ≫ i.I.ι)),
        HomologicalComplex.homologyMap
          (((galoisGlobalSections Λ (Over.mk j.toBase) kbar).mapHomologicalComplex _).map φ)
            m = 0) ∧
      (∀ (IP : CochainComplex.InjectiveResolution
          ((CochainComplex.singleFunctor (EtaleModules.{u, 0} Λ (Over.mk j.toBase).left) 0).obj
            ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj
              ((representationSheaf B X x Λ).obj P))))
        (φ : IP.cocomplex ⟶ i.I.cocomplex)
        (_ : (IP.ι ≫ φ = (CochainComplex.singleFunctor _ 0).map
          ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).map
            ((representationSheaf B X x Λ).map π)) ≫ i.I.ι)),
        HomologicalComplex.homologyMap
          (((galoisGlobalSections Λᵐᵒᵖ (Over.mk j.toBase) kbar).mapHomologicalComplex _).map
            (Stacks.AbelianInternalHom.homOpComplexPrecomp
              (M := etaleHomOpTarget (Over.mk j.toBase) Kc) φ)) (2 - m) = 0) := by
  by_cases hneg : m < 0
  · refine ⟨i.M, 𝟙 _, inferInstance, fun IP _ φ _ => ?_, fun IP φ _ => ?_⟩
    · exact (isZero_homology_galoisHomOpA_of_neg kbar
        (PoincareIndex.mk' (j := j) i.M IP.cocomplex IP.ι) m hneg).eq_of_src _ _
    · exact (hE i (2 - m) (Or.inr (by omega))).eq_of_src _ _
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℤ) = 1 - m := ⟨(1 - m).toNat, Int.toNat_of_nonneg (by omega)⟩
    obtain ⟨c⟩ := hcoeff.nonempty i.M n
    obtain ⟨N', π', hπ', hprop⟩ := hD (n + 1) (by omega) (by omega) c.P
    have := c.epi
    refine ⟨N', π' ≫ c.π, epi_comp _ _, fun IP _ φ hφ => ?_, fun IP φ hφ => ?_⟩
    · have h := homologyMap_galoisHomOpA_eq_zero B X x Λ f j kbar (n + 1) (by omega) (π' ≫ c.π)
        (by rw [Functor.map_comp, c.map_π, comp_zero]) IP i.I φ hφ
      rwa [show ((2 - (n + 1) : ℕ) : ℤ) = m by omega] at h
    · have h := hprop i.M c.π i.I IP φ hφ
      rwa [show ((n + 1 : ℕ) : ℤ) = 2 - m by omega] at h

set_option maxHeartbeats 400000 in
-- elaborating the injective-resolution hypotheses and the `Γ^Gal` short exact sequences
omit [IsCurve k f] [Smooth f] [GeometricallyConnected f] [IsAlgClosed kbar]
  [CompactSpace (kbar ≃ₐ[k] kbar)] in
/-- **The inductive step for the family**: a coeffacing epimorphism `π : P ⟶ M` gives members
`i₁, i₂` of the family and short exact sequences `Γ^Gal(I₁) → Γ^Gal(I₂) → Γ^Gal(I)` and
`Γ^Gal(ℋom^•(I, K)) → Γ^Gal(ℋom^•(I₂, K)) → Γ^Gal(ℋom^•(I₁, K))` compatible with the pairings,
the map `Γ^Gal(I₂) → Γ^Gal(I)` being zero on `H^m` and the map
`Γ^Gal(ℋom^•(I, K)) → Γ^Gal(ℋom^•(I₂, K))` zero on `H^{2-m}`. -/
lemma poincarePairing_step (i : PoincareIndex B X x Λ f j) (m : ℤ)
    (P : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x))
    (π : P ⟶ i.M) (hπ : Epi π)
    (hA0 : (∀ (IP : CochainComplex.InjectiveResolution
          ((CochainComplex.singleFunctor (EtaleModules.{u, 0} Λ (Over.mk j.toBase).left) 0).obj
            ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj
              ((representationSheaf B X x Λ).obj P))))
        [IP.cocomplex.IsStrictlyGE 0]
        (φ : IP.cocomplex ⟶ i.I.cocomplex) (_ : (IP.ι ≫ φ = (CochainComplex.singleFunctor _ 0).map
          ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).map
            ((representationSheaf B X x Λ).map π)) ≫ i.I.ι)),
        HomologicalComplex.homologyMap
          (((galoisGlobalSections Λ (Over.mk j.toBase) kbar).mapHomologicalComplex _).map φ)
            m = 0))
    (hE0 : (∀ (IP : CochainComplex.InjectiveResolution
          ((CochainComplex.singleFunctor (EtaleModules.{u, 0} Λ (Over.mk j.toBase).left) 0).obj
            ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj
              ((representationSheaf B X x Λ).obj P))))
        (φ : IP.cocomplex ⟶ i.I.cocomplex)
        (_ : (IP.ι ≫ φ = (CochainComplex.singleFunctor _ 0).map
          ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).map
            ((representationSheaf B X x Λ).map π)) ≫ i.I.ι)),
        HomologicalComplex.homologyMap
          (((galoisGlobalSections Λᵐᵒᵖ (Over.mk j.toBase) kbar).mapHomologicalComplex _).map
            (Stacks.AbelianInternalHom.homOpComplexPrecomp
              (M := etaleHomOpTarget (Over.mk j.toBase) Kc) φ)) (2 - m) = 0)) :
    ∃ (i₁ i₂ : PoincareIndex B X x Λ f j)
      (f₁ : galoisHomOpA (Over.mk j.toBase) kbar i₁.I.cocomplex ⟶
        galoisHomOpA (Over.mk j.toBase) kbar i₂.I.cocomplex)
      (f₂ : galoisHomOpA (Over.mk j.toBase) kbar i₂.I.cocomplex ⟶
        galoisHomOpA (Over.mk j.toBase) kbar i.I.cocomplex)
      (g₁ : galoisHomOpE (Over.mk j.toBase) kbar i.I.cocomplex Kc ⟶
        galoisHomOpE (Over.mk j.toBase) kbar i₂.I.cocomplex Kc)
      (g₂ : galoisHomOpE (Over.mk j.toBase) kbar i₂.I.cocomplex Kc ⟶
        galoisHomOpE (Over.mk j.toBase) kbar i₁.I.cocomplex Kc)
      (w₁ : f₁ ≫ f₂ = 0) (w₂ : g₁ ≫ g₂ = 0),
      (ShortComplex.mk f₁ f₂ w₁).ShortExact ∧ (ShortComplex.mk g₁ g₂ w₂).ShortExact ∧
      (∀ (n p q : ℤ) (hpq : p + n = q)
        (a : ((galoisHomOpA (Over.mk j.toBase) kbar i₁.I.cocomplex).X n).obj.obj.V)
        (e : ((galoisHomOpE (Over.mk j.toBase) kbar i₂.I.cocomplex Kc).X p).obj.obj.V),
        (poincarePairing kbar Kc t i₂).pair n p q hpq ((f₁.f n).hom.hom.hom.hom a) e =
          (poincarePairing kbar Kc t i₁).pair n p q hpq a ((g₂.f p).hom.hom.hom.hom e)) ∧
      (∀ (n p q : ℤ) (hpq : p + n = q)
        (a : ((galoisHomOpA (Over.mk j.toBase) kbar i₂.I.cocomplex).X n).obj.obj.V)
        (e : ((galoisHomOpE (Over.mk j.toBase) kbar i.I.cocomplex Kc).X p).obj.obj.V),
        (poincarePairing kbar Kc t i).pair n p q hpq ((f₂.f n).hom.hom.hom.hom a) e =
          (poincarePairing kbar Kc t i₂).pair n p q hpq a ((g₁.f p).hom.hom.hom.hom e)) ∧
      HomologicalComplex.homologyMap f₂ m = 0 ∧ HomologicalComplex.homologyMap g₁ (2 - m) = 0 := by
  have := i.ge
  let S := ShortComplex.mk (kernel.ι π) π (kernel.condition π)
  have hS : S.ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_kernel π) inferInstance hπ
  have := preservesFiniteLimits_representationSheaf B X x Λ
  have := preservesFiniteColimits_representationSheaf B X x Λ
  have hS' := hS.map_of_exact (representationSheaf B X x Λ ⋙
    etaleModuleExtensionByZero.{u, 0} Λ j.immersion)
  obtain ⟨T₁, T₂, fh, gh, w, ι₁, ι₂, hge₁, hge₂, hinj₁, hinj₂, hq₁, hq₂, hse, hc₁, hc₂, hsplit⟩ :=
    hS'.exists_horseshoe_of_resolution i.I.cocomplex i.I.ι
  have := hge₁; have := hge₂; have := hinj₁; have := hinj₂; have := hq₁; have := hq₂
  have hSE := shortExact_galoisHomOp_of_splitting (Over.mk j.toBase) kbar Kc
    (ShortComplex.mk fh gh w) hsplit
  refine ⟨PoincareIndex.mk' (j := j) (kernel π) T₁ ι₁, PoincareIndex.mk' (j := j) P T₂ ι₂,
    ((galoisGlobalSections Λ (Over.mk j.toBase) kbar).mapHomologicalComplex _).map fh,
    ((galoisGlobalSections Λ (Over.mk j.toBase) kbar).mapHomologicalComplex _).map gh,
    ((galoisGlobalSections Λᵐᵒᵖ (Over.mk j.toBase) kbar).mapHomologicalComplex _).map
      (Stacks.AbelianInternalHom.homOpComplexPrecomp
        (M := etaleHomOpTarget (Over.mk j.toBase) Kc) gh),
    ((galoisGlobalSections Λᵐᵒᵖ (Over.mk j.toBase) kbar).mapHomologicalComplex _).map
      (Stacks.AbelianInternalHom.homOpComplexPrecomp
        (M := etaleHomOpTarget (Over.mk j.toBase) Kc) fh),
    galoisHomOpA_map_comp_eq_zero kbar fh gh w, galoisHomOpE_map_comp_eq_zero kbar Kc fh gh w,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hSE.1
  · exact hSE.2
  · exact poincarePairing_precomp kbar Kc t (PoincareIndex.mk' (j := j) P T₂ ι₂)
      (PoincareIndex.mk' (j := j) (kernel π) T₁ ι₁) fh
  · exact poincarePairing_precomp kbar Kc t i (PoincareIndex.mk' (j := j) P T₂ ι₂) gh
  · exact @hA0 (PoincareIndex.mk' (j := j) P T₂ ι₂).I hge₂ gh hc₂
  · exact hE0 (PoincareIndex.mk' (j := j) P T₂ ι₂).I gh hc₂

/-- **The Poincaré pairings of the family are quasi-isomorphisms**, given the base case in
degree `2`, the vanishing of the cohomology of `Γ^Gal(ℋom^•(I, K))` outside `[0, 2]`, and
coeffacements of the cohomological side. -/
theorem quasiIso_poincarePairing
    (hcoeff : (compactSupportRepresentationHomology B X x Λ f j kbar).Coeffaceable)
    (hbase : ∀ i : PoincareIndex B X x Λ f j, IsIso (HomologicalComplex.homologyMap
      (Stacks.ContinuousCohomology.internalHomComplexOfPairing (poincarePairing kbar Kc t i)) 2))
    (hE : ∀ (i : PoincareIndex B X x Λ f j) (q : ℤ), (q < 0 ∨ 2 < q) →
      IsZero ((galoisHomOpE (Over.mk j.toBase) kbar i.I.cocomplex Kc).homology q))
    (hD : ∀ (n : ℕ), 1 ≤ n → n ≤ 2 →
      ∀ N : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x),
      ∃ (N' : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x))
        (π' : N' ⟶ N), Epi π' ∧
      ∀ (M : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x))
        (π : N ⟶ M)
        (IM : CochainComplex.InjectiveResolution
          ((CochainComplex.singleFunctor (EtaleModules.{u, 0} Λ (Over.mk j.toBase).left) 0).obj
            ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj
              ((representationSheaf B X x Λ).obj M))))
        (IN : CochainComplex.InjectiveResolution
          ((CochainComplex.singleFunctor (EtaleModules.{u, 0} Λ (Over.mk j.toBase).left) 0).obj
            ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj
              ((representationSheaf B X x Λ).obj N'))))
        (φ : IN.cocomplex ⟶ IM.cocomplex)
        (_ : (IN.ι ≫ φ = (CochainComplex.singleFunctor _ 0).map
          ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).map
            ((representationSheaf B X x Λ).map (π' ≫ π))) ≫ IM.ι)),
        HomologicalComplex.homologyMap
          (((galoisGlobalSections Λᵐᵒᵖ (Over.mk j.toBase) kbar).mapHomologicalComplex _).map
            (Stacks.AbelianInternalHom.homOpComplexPrecomp
              (M := etaleHomOpTarget (Over.mk j.toBase) Kc) φ)) (n : ℤ) = 0)
    (i : PoincareIndex B X x Λ f j) :
    QuasiIso
      (Stacks.ContinuousCohomology.internalHomComplexOfPairing (poincarePairing kbar Kc t i)) :=
  Stacks.ContinuousCohomology.quasiIso_internalHomComplexOfPairing_of_coeffacement.{u, u + 1}
    (fun i : PoincareIndex B X x Λ f j => galoisHomOpA (Over.mk j.toBase) kbar i.I.cocomplex)
    (fun i => galoisHomOpE (Over.mk j.toBase) kbar i.I.cocomplex Kc)
    (poincarePairing kbar Kc t) hbase
    (fun i m hm => isZero_homology_galoisHomOpA_of_two_lt f j kbar Λ _ i.I m hm)
    (fun i m hm => hE i (2 - m) (Or.inl (by omega)))
    (fun i m hm => by
      obtain ⟨P, π, hπ, hA0, hE0⟩ := exists_poincareCoeffacingEpi kbar Kc hcoeff hE hD i m hm
      exact poincarePairing_step kbar Kc t i m P π hπ hA0 hE0) i

end AlgebraicGeometry

end
