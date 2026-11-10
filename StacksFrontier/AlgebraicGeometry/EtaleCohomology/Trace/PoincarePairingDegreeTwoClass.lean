module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportResolutionIntModel
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportDegreeZeroBridgeTrace
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GaloisCompactSupportTrace

/-!
# The degree-zero class of a cocycle in the base case of Tag 03VM

For a member `(M, I)` of the Poincaré family and an injective resolution `K₀` of `j_! μ_n` on the
compactification, `n = #Λ`, a degree-zero cocycle `β` of `Γ^Gal(ℋom^•_ℤ(I, res_ℤ K₀))` acts
on the restrictions `I|_{X̄_k̄} ⟶ K₀|_{X̄_k̄}` (`Stacks.EtaleCohomology.galoisHomOpCocycleAct`),
over a map `θ_β : res_ℤ((j_! ℱ_M)|) ⟶ res_ℤ((j_! μ_n)|)`
(`Stacks.EtaleCohomology.galoisHomOpCocycleH0`).
Its restriction to `X_k̄` is an element of `Hom_{π₁(X_k̄)}(M, μ_n)`
(`AlgebraicGeometry.poincareDegreeZeroClass`).

## Main definitions

* `Stacks.EtaleCohomology.galoisBaseChangeRestrictScalarsIso`:
  `(res_ℤ K₀)|_{Y_K} ≅ res_ℤ(K₀|_{Y_K})`.
* `AlgebraicGeometry.poincareCocycleH0`, `AlgebraicGeometry.poincareDegreeZeroClass`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

/-- **Restriction of scalars along `ℤ → ℤ` is the identity**, on sections. -/
def etaleModuleRestrictScalarsIntSelfIso (Y : Scheme.{u}) :
    etaleModuleRestrictScalars (Int.castRingHom ℤ) Y ≅ 𝟭 _ :=
  NatIso.ofComponents (fun N => ObjectProperty.isoMk _ (Functor.isoWhiskerLeft N.obj
      (ModuleCat.restrictScalarsId'.{u + 1} (Int.castRingHom ℤ) (RingHom.ext_int _ _))))
    (fun _ => by ext; rfl)

section Glue

variable {k : Type u} [Field k] (Y : Over (Spec (.of k))) (K : Type u) [Field K] [Algebra k K]
  {R : Type} [Ring R]

/-- The comparison `((res_ℤ G)|_{Y_K} read over ℤ) ≅ res_ℤ(G|_{Y_K})`: restriction of scalars along
`ℤ → ℤ` is the identity and inverse image commutes with `res_ℤ`. -/
def galoisBaseChangeRestrictScalarsNatIso :
    etaleModuleRestrictScalars (Int.castRingHom R) Y.left ⋙
        (etaleModuleInverseImage.{u, 0} ℤ (fieldBaseChangeProj Y K) ⋙
          etaleModuleRestrictScalars (Int.castRingHom ℤ) (fieldBaseChange Y K)) ≅
      etaleModuleInverseImage.{u, 0} R (fieldBaseChangeProj Y K) ⋙
        etaleModuleRestrictScalars (Int.castRingHom R) (fieldBaseChange Y K) :=
  Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _
      (etaleModuleRestrictScalarsIntSelfIso (fieldBaseChange Y K)) ≪≫ Functor.rightUnitor _) ≪≫
    etaleModuleInverseImageRestrictScalars (Int.castRingHom R) (fieldBaseChangeProj Y K)

/-- **`(res_ℤ K₀)|_{Y_K} ≅ res_ℤ(K₀|_{Y_K})`** for a complex `K₀` of sheaves of `R`-modules. -/
def galoisBaseChangeRestrictScalarsIso (K₀ : CochainComplex (EtaleModules.{u, 0} R Y.left) ℤ) :
    galoisBaseChangeComplex Y K
        (((etaleModuleRestrictScalars (Int.castRingHom R) Y.left).mapHomologicalComplex _).obj K₀) ≅
      ((etaleModuleRestrictScalars (Int.castRingHom R) (fieldBaseChange Y K)).mapHomologicalComplex
        _).obj (((etaleModuleInverseImage.{u, 0} R (fieldBaseChangeProj Y K)).mapHomologicalComplex
          _).obj K₀) :=
  (NatIso.mapHomologicalComplex (galoisBaseChangeRestrictScalarsNatIso Y K) _).app K₀

end Glue

section Augmentation

attribute [local instance] HasDerivedCategory.standard

variable {Λ : Type} [Ring Λ] {k : Type u} [Field k] {X : Scheme.{u}}
  {f : X ⟶ Spec (.of k)} {j : CompactificationOf (Over.mk f)}
  (kbar : Type u) [Field kbar] [Algebra k kbar] [Algebra.IsSeparable k kbar]

/-- The augmentation `res_ℤ((j_! F)|)[0] ⟶ res_ℤ(I|)` is a quasi-isomorphism. -/
instance quasiIso_compactSupportResolutionIntAugmentation_hom (F : EtaleModules.{u, 0} Λ X)
    (I : CochainComplex.InjectiveResolution ((CochainComplex.singleFunctor _ 0).obj
      ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F))) :
    QuasiIso (compactSupportResolutionIntAugmentation kbar F I).hom := by
  have h :
      IsIso (DerivedCategory.Plus.Q.map (compactSupportResolutionIntAugmentation kbar F I)) := by
    rw [← compactSupportResolutionIntSingleIso_hom]
    exact Iso.isIso_hom _
  have h' : IsIso (DerivedCategory.Q.map (compactSupportResolutionIntAugmentation kbar F I).hom) :=
    inferInstanceAs (IsIso (DerivedCategory.Plus.ι.map
      (DerivedCategory.Plus.Q.map (compactSupportResolutionIntAugmentation kbar F I))))
  exact (DerivedCategory.isIso_Q_map_iff_quasiIso
    (φ := (compactSupportResolutionIntAugmentation kbar F I).hom)).1 h'

end Augmentation

end Stacks.EtaleCohomology


namespace AlgebraicGeometry

open Stacks.GroupCohomology Stacks.EtaleCohomology

/-- `#Λ ≠ 0` for a finite ring. -/
local instance neZero_fintypeCard_poincareClass (Λ : Type) [Ring Λ] [Fintype Λ] :
    NeZero (Fintype.card Λ) :=
  ⟨Fintype.card_ne_zero⟩

variable (B : BigEtaleSite.{u}) (X : B.Scheme) {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k))
  [IsCurve k f] [Smooth f] [GeometricallyConnected f] (kbar : Type u) [Field kbar]
  [Algebra k kbar] [IsAlgClosed kbar] [Algebra.IsAlgebraic k kbar] [Algebra.IsSeparable k kbar]
  [CompactSpace (kbar ≃ₐ[k] kbar)]
  (Λ : Type) [Ring Λ] [Fintype Λ] [Algebra (ZMod (Fintype.card Λ)) Λ]
  (y : GeometricPoint (fieldBaseChange (Over.mk f) kbar)) (j : CompactificationOf (Over.mk f))
  (K₀ : letI := connectedSpace_of_isCurve B X f
    CochainComplex.InjectiveResolution
      ((CochainComplex.singleFunctor _ 0).obj
        ((etaleModuleExtensionByZero (ZMod (Fintype.card Λ)) j.immersion).obj
          ((representationSheaf B X _ (ZMod (Fintype.card Λ))).obj
            (cyclotomicContinuousModule B X f kbar y (Fintype.card Λ))))))

/-- The augmentation of the restricted resolution `I|_{X̄_k̄}` of a member of the Poincaré
family, read over `ℤ`. -/
def poincareAugmentationL (i : letI := connectedSpace_of_isCurve B X f
      PoincareIndex B X (y.map (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ f j) :
    letI := connectedSpace_of_isCurve B X f
    (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
        ((etaleModuleRestrictScalars (Int.castRingHom Λ)
          (pullback j.toBase (specAlgebraMap k kbar))).obj
          ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst j.toBase (specAlgebraMap k kbar))).obj
            ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj
              ((representationSheaf B X _ Λ).obj i.M)))) ⟶
      galoisBaseChangeComplex (Over.mk j.toBase) kbar i.I.cocomplex :=
  letI := connectedSpace_of_isCurve B X f
  (compactSupportResolutionIntAugmentation kbar ((representationSheaf B X _ Λ).obj i.M) i.I).hom

/-- The augmentation `poincareAugmentationL` is a quasi-isomorphism. -/
instance quasiIso_poincareAugmentationL (i : letI := connectedSpace_of_isCurve B X f
      PoincareIndex B X (y.map (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ f j) :
    QuasiIso (poincareAugmentationL B X f kbar Λ y j i) :=
  quasiIso_compactSupportResolutionIntAugmentation_hom kbar _ _

/-- The augmentation of the restricted resolution `K₀|_{X̄_k̄}` of `j_! μ_n`, read over `ℤ`, into
`(res_ℤ K₀)|_{X̄_k̄}`. -/
def poincareAugmentationK :
    letI := connectedSpace_of_isCurve B X f
    (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
        ((etaleModuleRestrictScalars (Int.castRingHom (ZMod (Fintype.card Λ)))
          (pullback j.toBase (specAlgebraMap k kbar))).obj
          ((etaleModuleInverseImage.{u, 0} (ZMod (Fintype.card Λ))
            (pullback.fst j.toBase (specAlgebraMap k kbar))).obj
            ((etaleModuleExtensionByZero.{u, 0} (ZMod (Fintype.card Λ)) j.immersion).obj
              ((representationSheaf B X _ (ZMod (Fintype.card Λ))).obj
                (cyclotomicContinuousModule B X f kbar y (Fintype.card Λ)))))) ⟶
      galoisBaseChangeComplex (Over.mk j.toBase) kbar
        (cyclotomicIntResolution B X f kbar y (Fintype.card Λ) j K₀) :=
  letI := connectedSpace_of_isCurve B X f
  (compactSupportResolutionIntAugmentation kbar _ K₀).hom ≫
    (galoisBaseChangeRestrictScalarsIso (Over.mk j.toBase) kbar K₀.cocomplex).inv

/-- The augmentation `poincareAugmentationK` is a quasi-isomorphism. -/
instance quasiIso_poincareAugmentationK : QuasiIso (poincareAugmentationK B X f kbar Λ y j K₀) := by
  let := connectedSpace_of_isCurve B X f
  exact quasiIso_comp _ _ (hφ := quasiIso_compactSupportResolutionIntAugmentation_hom kbar _ K₀)
    (hφ' := @quasiIso_of_isIso _ _ _ _ _ _ _ _ (Iso.isIso_inv _) _ _)

omit [Fintype Λ] [Algebra (ZMod (Fintype.card Λ)) Λ] in
/-- The restriction to `X̄_k̄` of the resolution `I` of a member of the Poincaré family, read over
`ℤ`, is concentrated in degrees `≥ 0`. -/
instance isStrictlyGE_galoisBaseChangeComplex_poincare [Finite Λ]
    (i : letI := connectedSpace_of_isCurve B X f
      PoincareIndex B X (y.map (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ f j) :
    letI := connectedSpace_of_isCurve B X f
    (galoisBaseChangeComplex (Over.mk j.toBase) kbar i.I.cocomplex).IsStrictlyGE 0 := by
  let := connectedSpace_of_isCurve B X f
  have := i.ge
  rw [CochainComplex.isStrictlyGE_iff]
  intro q hq
  exact Functor.map_isZero (etaleModuleInverseImage.{u, 0} Λ
      (fieldBaseChangeProj (Over.mk j.toBase) kbar) ⋙
        etaleModuleRestrictScalars (Int.castRingHom Λ) _)
    (CochainComplex.isZero_of_isStrictlyGE i.I.cocomplex 0 q hq)

/-- The restriction to `X̄_k̄` of `res_ℤ K₀` is concentrated in degrees `≥ 0` when `K₀` is. -/
instance isStrictlyGE_galoisBaseChangeComplex_cyclotomic [K₀.cocomplex.IsStrictlyGE 0] :
    (galoisBaseChangeComplex (Over.mk j.toBase) kbar
      (cyclotomicIntResolution B X f kbar y (Fintype.card Λ) j K₀)).IsStrictlyGE 0 := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro q hq
  exact Functor.map_isZero (etaleModuleInverseImage.{u, 0} ℤ
      (fieldBaseChangeProj (Over.mk j.toBase) kbar) ⋙
        etaleModuleRestrictScalars (Int.castRingHom ℤ) _)
    (Functor.map_isZero (etaleModuleRestrictScalars (Int.castRingHom (ZMod (Fintype.card Λ))) _)
      (CochainComplex.isZero_of_isStrictlyGE K₀.cocomplex 0 q hq))

variable [K₀.cocomplex.IsStrictlyGE 0]

/-- **`θ_β`**: the map `res_ℤ((j_! ℱ_M)|_{X̄_k̄}) ⟶ res_ℤ((j_! μ_n)|_{X̄_k̄})` under the morphism
of complexes of a degree-zero cocycle `β` of `Γ^Gal(ℋom^•_ℤ(I, res_ℤ K₀))`. -/
def poincareCocycleH0 (i : letI := connectedSpace_of_isCurve B X f
      PoincareIndex B X (y.map (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ f j)
    (β : letI := connectedSpace_of_isCurve B X f
      ((galoisHomOpE (Over.mk j.toBase) kbar i.I.cocomplex
      (cyclotomicIntResolution B X f kbar y (Fintype.card Λ) j K₀)).X 0).obj.obj.V)
    (hβ : letI := connectedSpace_of_isCurve B X f
      ((galoisHomOpE (Over.mk j.toBase) kbar i.I.cocomplex
      (cyclotomicIntResolution B X f kbar y (Fintype.card Λ) j K₀)).d 0 1).hom.hom.hom.hom β = 0) :
    letI := connectedSpace_of_isCurve B X f
    (etaleModuleRestrictScalars (Int.castRingHom Λ) (pullback j.toBase (specAlgebraMap k kbar))).obj
        ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst j.toBase (specAlgebraMap k kbar))).obj
          ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj
            ((representationSheaf B X _ Λ).obj i.M))) ⟶
      (etaleModuleRestrictScalars (Int.castRingHom (ZMod (Fintype.card Λ)))
        (pullback j.toBase (specAlgebraMap k kbar))).obj
        ((etaleModuleInverseImage.{u, 0} (ZMod (Fintype.card Λ))
          (pullback.fst j.toBase (specAlgebraMap k kbar))).obj
          ((etaleModuleExtensionByZero.{u, 0} (ZMod (Fintype.card Λ)) j.immersion).obj
            ((representationSheaf B X _ (ZMod (Fintype.card Λ))).obj
              (cyclotomicContinuousModule B X f kbar y (Fintype.card Λ))))) :=
  letI := connectedSpace_of_isCurve B X f
  haveI := quasiIso_poincareAugmentationL B X f kbar Λ y j i
  haveI := quasiIso_poincareAugmentationK B X f kbar Λ y j K₀
  haveI := isStrictlyGE_galoisBaseChangeComplex_poincare B X f kbar Λ y j i
  haveI := isStrictlyGE_galoisBaseChangeComplex_cyclotomic B X f kbar Λ y j K₀
  galoisHomOpCocycleH0 (Over.mk j.toBase) kbar i.I.cocomplex
    (cyclotomicIntResolution B X f kbar y (Fintype.card Λ) j K₀)
    (poincareAugmentationL B X f kbar Λ y j i) (poincareAugmentationK B X f kbar Λ y j K₀) β hβ

/-- **The degree-zero class of a cocycle**: the element of `Hom_{π₁(X_k̄)}(M, μ_n)` corresponding
to the restriction to `X_k̄` of the `ℤ/n`-linear lift of `θ_β`. -/
def poincareDegreeZeroClass (i : letI := connectedSpace_of_isCurve B X f
      PoincareIndex B X (y.map (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ f j)
    (β : letI := connectedSpace_of_isCurve B X f
      ((galoisHomOpE (Over.mk j.toBase) kbar i.I.cocomplex
      (cyclotomicIntResolution B X f kbar y (Fintype.card Λ) j K₀)).X 0).obj.obj.V)
    (hβ : letI := connectedSpace_of_isCurve B X f
      ((galoisHomOpE (Over.mk j.toBase) kbar i.I.cocomplex
      (cyclotomicIntResolution B X f kbar y (Fintype.card Λ) j K₀)).d 0 1).hom.hom.hom.hom β = 0) :
    letI := connectedSpace_of_isCurve B X f
    (geometricCyclotomicDualInvariants B X f kbar Λ y).obj (Opposite.op i.M) :=
  letI := connectedSpace_of_isCurve B X f
  geometricCyclotomicDualHomEquiv B X f kbar Λ y i.M
    (compactSupportOpenRestriction f j kbar (algebraMap (ZMod (Fintype.card Λ)) Λ) _ _
      (restrictScalarsIntLift (algebraMap (ZMod (Fintype.card Λ)) Λ) _ ZMod.intCast_surjective
        (poincareCocycleH0 B X f kbar Λ y j K₀ i β hβ)))

omit [CompactSpace (kbar ≃ₐ[k] kbar)] in
/-- Unfolding `poincareDegreeZeroClass`. -/
lemma poincareDegreeZeroClass_eq (i : letI := connectedSpace_of_isCurve B X f
      PoincareIndex B X (y.map (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ f j)
    (β : letI := connectedSpace_of_isCurve B X f
      ((galoisHomOpE (Over.mk j.toBase) kbar i.I.cocomplex
      (cyclotomicIntResolution B X f kbar y (Fintype.card Λ) j K₀)).X 0).obj.obj.V)
    (hβ : letI := connectedSpace_of_isCurve B X f
      ((galoisHomOpE (Over.mk j.toBase) kbar i.I.cocomplex
      (cyclotomicIntResolution B X f kbar y (Fintype.card Λ) j K₀)).d 0 1).hom.hom.hom.hom β = 0) :
    letI := connectedSpace_of_isCurve B X f
    poincareDegreeZeroClass B X f kbar Λ y j K₀ i β hβ =
      geometricCyclotomicDualHomEquiv B X f kbar Λ y i.M
        (compactSupportOpenRestriction f j kbar (algebraMap (ZMod (Fintype.card Λ)) Λ) _ _
          (restrictScalarsIntLift (algebraMap (ZMod (Fintype.card Λ)) Λ) _ ZMod.intCast_surjective
            (poincareCocycleH0 B X f kbar Λ y j K₀ i β hβ))) :=
  rfl

omit [Smooth f] [CompactSpace (kbar ≃ₐ[k] kbar)] [Algebra (ZMod (Fintype.card Λ)) Λ]
  [K₀.cocomplex.IsStrictlyGE 0] in
/-- The underlying element of a degree-zero cycle of the underlying complex of `Γ^Gal(ℋom^•(I, K))`
is a cocycle. -/
lemma galoisHomOpE_d_iCycles_zero (i : letI := connectedSpace_of_isCurve B X f
      PoincareIndex B X (y.map (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ f j)
    (z : letI := connectedSpace_of_isCurve B X f
      (Stacks.ContinuousCohomology.underlyingAb.{0, u, u + 1} Λᵐᵒᵖ
        (galoisHomOpE (Over.mk j.toBase) kbar i.I.cocomplex
          (cyclotomicIntResolution B X f kbar y (Fintype.card Λ) j K₀))).cycles 0) :
    letI := connectedSpace_of_isCurve B X f
    ((galoisHomOpE (Over.mk j.toBase) kbar i.I.cocomplex
      (cyclotomicIntResolution B X f kbar y (Fintype.card Λ) j K₀)).d 0 1).hom.hom.hom.hom
        (((Stacks.ContinuousCohomology.underlyingAb.{0, u, u + 1} Λᵐᵒᵖ
          (galoisHomOpE (Over.mk j.toBase) kbar i.I.cocomplex
            (cyclotomicIntResolution B X f kbar y (Fintype.card Λ) j K₀))).iCycles 0).hom z) = 0 :=
  let := connectedSpace_of_isCurve B X f
  ConcreteCategory.congr_hom ((Stacks.ContinuousCohomology.underlyingAb.{0, u, u + 1} Λᵐᵒᵖ
    (galoisHomOpE (Over.mk j.toBase) kbar i.I.cocomplex
      (cyclotomicIntResolution B X f kbar y (Fintype.card Λ) j K₀))).iCycles_d 0 1) z

end AlgebraicGeometry

end
