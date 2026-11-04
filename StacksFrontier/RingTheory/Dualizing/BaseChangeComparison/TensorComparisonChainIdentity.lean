module

public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorComparisonChainIdentityGlue
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorComparisonChainIdentityVanishing

/-!
# The chain-level identity behind [stacks 0E2A]

`Dualizing.chainIdentity`: for a resolution `p : P → A` over `R`, a complex `K` of `R`-modules and
a tensor base-change isomorphism `e`, the base change to `R'` of `𝟙 ⊗ p` followed by the
projection formula over `R`, the comparison of [stacks 0661], the two composition isomorphisms
of extensions of scalars and the projection formula over `R'`, is `𝟙 ⊗ p'` for the base-changed
resolution `p'` of `A ⊗_R R'`.

## Implementation notes

The identity is checked on the pure tensors `(1 ⊗ k) ⊗ (1 ⊗ z)` of each summand.  Every map is
evaluated through `Dualizing.evalB`, which fixes one spelling of the universe levels of the
`R'`-modules involved, and the values of the maps are chained inner-out.  Without this the kernel
does not finish identifying the many spellings of the same universe levels that the maps carry.

## References

* [Stacks Project, Tag 0E2A](https://stacks.math.columbia.edu/tag/0E2A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits StacksDraft.DerivedHom
open CochainComplex.DerivedExtensionScalars CochainComplex.DerivedTensor
open scoped ChangeOfRings

attribute [local instance] HasDerivedCategory.standard

namespace Dualizing

universe uR uA uRp v

attribute [local instance] Algebra.TensorProduct.rightAlgebra
attribute [local instance] extendScalarsAdditiveOfRingHom

variable {R : Type uR} {A : Type uA} {R' : Type uRp} [CommRing R] [CommRing A] [CommRing R']
  [Algebra R A] [Algebra R R']
  (hTor : RingTheory.TorIndependence.TorIndependent R A R')
  (baseChangeR :
    DerivedCategory (ModuleCat.{max v uR uA uRp} R) ⥤
      DerivedCategory (ModuleCat.{max v uR uA uRp} R'))
  (comparisonR :
    DerivedCategory.Q ⋙ baseChangeR ⟶
      (ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
        (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  (baseChangeA :
    DerivedCategory (ModuleCat.{max v uR uA uRp} A) ⥤
      DerivedCategory (ModuleCat.{max v uR uA uRp} (TensorProduct R A R')))
  (comparisonA :
    DerivedCategory.Q ⋙ baseChangeA ⟶
      (ModuleCat.extendScalars.{uA, max uA uRp, max v uR uA uRp}
        (algebraMap A (TensorProduct R A R'))).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)

variable [hA : baseChangeA.IsLeftDerivedFunctor comparisonA
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp} A) (ComplexShape.up ℤ))]
  [hR : baseChangeR.IsLeftDerivedFunctor comparisonR
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp} R) (ComplexShape.up ℤ))]

variable (P : CochainComplex (ModuleCat.{max v uR uA uRp} R) ℤ)
  (hP : CochainComplex.KFlat.{uR, max v uA uRp} P)
  (p : P ⟶ algebraComplex.{max v uRp} (algebraMap R A)) [QuasiIso p]

/-- An element of a degree of a complex, read in the restriction of scalars of that complex. -/
def resC.{u₁, u₂, w} {S : Type u₁} {T : Type u₂} [Ring S] [Ring T] (φ : S →+* T)
    (X : CochainComplex (ModuleCat.{w} T) ℤ) (i : ℤ) (x : X.X i) :
    (((ModuleCat.restrictScalars.{w} φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj X).X i :=
  x

/-- `Dualizing.chainIdentity_piece₁`, with its value read through `Dualizing.resC`. -/
theorem chainIdentity_piece₁' (K : CochainComplex (ModuleCat.{max v uR uA uRp} R) ℤ) (a : ℤ)
    (hab : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (a, 0) = a)
    (k : K.X a) (z : P.X 0) : ((((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
        (algebraMap R R')).mapHomologicalComplex
          (ComplexShape.up ℤ)).map
        (HomologicalComplex.mapBifunctorMap (𝟙 K) p (moduleTensor.{uR, max (max v uRp) uR uA} R)
          (ComplexShape.up ℤ) ≫ (extendRestrictComplexIso.{max v uRp} (algebraMap R A) K).inv)).f
              a).hom
        (bcTmulC.{uR, uRp, max v uR uA uRp} (algebraMap R R')
          (HomologicalComplex.mapBifunctor K P (moduleTensor.{uR, max (max v uRp) uR uA} R)
            (ComplexShape.up ℤ)) a 1
          ((HomologicalComplex.ιMapBifunctor K P (moduleTensor.{uR, max (max v uRp) uR uA} R)
            (ComplexShape.up ℤ) a 0 a hab).hom (k ⊗ₜ[R] z))) =
      bcTmulC.{uR, uRp, max v uR uA uRp} (algebraMap R R')
          (((ModuleCat.restrictScalars.{max v uR uA uRp} (algebraMap R A)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj (((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp}
          (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) a 1
        (resC.{uR, uA, max v uR uA uRp} (algebraMap R A)
            (((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp}
            (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) a
          (bcTmul.{uR, uA, max v uR uA uRp} (algebraMap R A)
            ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          (algebraModule.{max v uRp} (algebraMap R A))).hom.hom ((p.f 0).hom z)).down k)) :=
  chainIdentity_piece₁ P p K a hab k z

/-- `Dualizing.chainIdentity_piece₂`, with its argument and value read through `Dualizing.resC`. -/
theorem chainIdentity_piece₂' (K : CochainComplex (ModuleCat.{max v uR uA uRp} R) ℤ) (a : ℤ)
    (u : A) (k : K.X a) :
    ((HomologicalComplex.Hom.f
        (chainBaseChangeComparison.{uR, uA, uRp, v} baseChangeR comparisonR baseChangeA
          comparisonA (((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp}
              (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) a)).hom
      (bcTmulC.{uR, uRp, max v uR uA uRp} (algebraMap R R')
          (((ModuleCat.restrictScalars.{max v uR uA uRp} (algebraMap R A)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj (((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp}
          (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) a 1
        (resC.{uR, uA, max v uR uA uRp} (algebraMap R A)
            (((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp}
            (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) a
          (bcTmul.{uR, uA, max v uR uA uRp} (algebraMap R A) u k))) =
      resC.{uRp, max uA uRp, max v uR uA uRp}
          (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R A R').toRingHom
        (((ModuleCat.extendScalars.{uA, max uA uRp, max v uR uA uRp}
          (algebraMap A (TensorProduct R A R'))).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp}
              (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) a
        (bcTmulC.{uA, max uA uRp, max v uR uA uRp} (algebraMap A (TensorProduct R A R'))
          (((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp}
              (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) a 1
          (bcTmul.{uR, uA, max v uR uA uRp} (algebraMap R A) u k)) :=
  chainIdentity_piece₂ baseChangeR comparisonR baseChangeA comparisonA
    (((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp} (algebraMap R A)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K) a (bcTmul.{uR, uA, max v uR uA uRp} (algebraMap R A) u k)

/-- A map of complexes after restriction of scalars, on elements read through `Dualizing.resC`. -/
theorem restrict_f_apply_resC.{u₁, u₂, w} {S : Type u₁} {T : Type u₂} [Ring S] [Ring T]
    (φ : S →+* T) {X Y : CochainComplex (ModuleCat.{w} T) ℤ} (f : X ⟶ Y) (a : ℤ) (x : X.X a)
    (y : Y.X a) (h : (f.f a).hom x = y) :
    ((((ModuleCat.restrictScalars.{w} φ).mapHomologicalComplex (ComplexShape.up ℤ)).map f).f a).hom
      (resC.{u₁, u₂, w} φ X a x) = resC.{u₁, u₂, w} φ Y a y :=
  h

/-- `Dualizing.chainIdentity_piece₃` after restriction of scalars, read through
`Dualizing.resC`. -/
theorem chainIdentity_piece₃' (K : CochainComplex (ModuleCat.{max v uR uA uRp} R) ℤ) (a : ℤ)
    (u : A) (k : K.X a) :
    ((((ModuleCat.restrictScalars.{max v uR uA uRp}
        (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R
        A R').toRingHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (chainExtendScalarsSwap.{uR, uA, uRp, v} K)).f a).hom
      (resC.{uRp, max uA uRp, max v uR uA uRp}
          (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R A R').toRingHom
        (((ModuleCat.extendScalars.{uA, max uA uRp, max v uR uA uRp}
          (algebraMap A (TensorProduct R A R'))).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp}
              (algebraMap R A)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K)) a
        (bcTmulC.{uA, max uA uRp, max v uR uA uRp} (algebraMap A (TensorProduct R A R'))
          (((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp}
              (algebraMap R A)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K) a 1
          (bcTmul.{uR, uA, max v uR uA uRp} (algebraMap R A) u k))) =
      resC.{uRp, max uA uRp, max v uR uA uRp}
          (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R A R').toRingHom
        (((ModuleCat.extendScalars.{uRp, max uA uRp, max v uR uA uRp}
            (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R
            A R').toRingHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
              (algebraMap R R')).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K)) a
        (bcTmulC.{uRp, max uA uRp, max v uR uA uRp}
            (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R A R').toRingHom
            (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
            (algebraMap R R')).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K) a
          (algebraMap A (TensorProduct R A R') u)
          (bcTmul.{uR, uRp, max v uR uA uRp} (algebraMap R R') 1 k)) :=
  restrict_f_apply_resC.{uRp, max uA uRp, max v uR uA uRp}
      (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R A R').toRingHom
    (chainExtendScalarsSwap.{uR, uA, uRp, v} K) a _ _ (chainIdentity_piece₃ K a u k)

/-- The pure tensor `(1 ⊗ k) ⊗ (1 ⊗ z)` of the tensor product of the base changes. -/
def tmulBC (K P : CochainComplex (ModuleCat.{max v uR uA uRp} R) ℤ) (a b : ℤ) (k : K.X a)
    (z : P.X b) : (((moduleTensor.{uRp, max (max v uR) uRp (max uA uRp)} R').obj
        ((((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
        (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj K).X a)).obj
        ((((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
        (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj P).X b)) :=
  bcTmulC.{uR, uRp, max v uR uA uRp} (algebraMap R R') K a 1 k ⊗ₜ[R']
    bcTmulC.{uR, uRp, max v uR uA uRp} (algebraMap R R') P b 1 z

/-- `Dualizing.extendScalars_tensor_hom_ext_complex` on the pure tensors `Dualizing.tmulBC`. -/
theorem extendScalars_tensor_hom_ext_tmulBC (K P : CochainComplex (ModuleCat.{max v uR uA uRp} R) ℤ)
    (a b : ℤ) {Z : ModuleCat.{max v uR uA uRp} R'}
    (α β : ((moduleTensor.{uRp, max (max v uR) uRp (max uA uRp)} R').obj
        ((((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
        (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj K).X a)).obj
        ((((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
        (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj P).X b) ⟶ Z)
    (h : ∀ (k : K.X a) (z : P.X b), α.hom (tmulBC.{uR, uA, uRp, v} K P a b k z) = β.hom
        (tmulBC.{uR, uA, uRp, v} K P a b k z)) :
    α = β :=
  extendScalars_tensor_hom_ext_complex.{uR, uA, uRp, v} (algebraMap R R') K P a b α β h

/-- The value of the chain identity on the summand of bidegree `(a, 0)`, typed in degree `a` of
`tensorComplex`. -/
def w6 (K : CochainComplex (ModuleCat.{max v uR uA uRp} R) ℤ) (a : ℤ) (t : TensorProduct R A R')
    (k : K.X a) :
    @HomologicalComplex.X ℤ (ModuleCat.{max v uR uA uRp} R') _ _ (ComplexShape.up ℤ)
      (tensorComplex.{uRp, max (max v uR) uA uRp}
          (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
          (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
        (algebraComplex.{max v uR} (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R
            A R').toRingHom)) a :=
  (HomologicalComplex.singleRightι (moduleTensor.{uRp, max (max v uR) uRp (max uA uRp)} R')
      (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp} (algebraMap R R')).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K)
          (algebraModule.{max v uR} (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R
              A R').toRingHom) a).hom
        (bcTmulC.{uR, uRp, max v uR uA uRp} (algebraMap R R') K a 1 k ⊗ₜ[R']
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
            (algebraModule.{max v uR} (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R
                A R').toRingHom)).inv.hom
            (ULift.up t : ULift.{max v uR uA uRp} (TensorProduct R A R')))

/-- `Dualizing.chainIdentity_piece₄` with its argument read through `Dualizing.resC`. -/
theorem chainIdentity_piece₄' (K : CochainComplex (ModuleCat.{max v uR uA uRp} R) ℤ) (a : ℤ)
    (t : TensorProduct R A R') (k : K.X a) :
    ((HomologicalComplex.Hom.f (A := (((ModuleCat.restrictScalars.{max v uR uA uRp}
        (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R
        A R').toRingHom).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((ModuleCat.extendScalars.{uRp, max uA uRp, max v uR uA uRp}
        (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R
        A R').toRingHom).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
        (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj K))))
        (extendRestrictComplexIso.{max v uR}
            (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R A R').toRingHom
            (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
            (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)).hom a)).hom
      (resC.{uRp, max uA uRp, max v uR uA uRp}
          (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R A R').toRingHom
        (((ModuleCat.extendScalars.{uRp, max uA uRp, max v uR uA uRp}
          (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R
              A R').toRingHom).mapHomologicalComplex (ComplexShape.up ℤ)).obj
              (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
              (algebraMap R R')).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K)) a
        (bcTmulC.{uRp, max uA uRp, max v uR uA uRp}
            (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R A R').toRingHom
            (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
            (algebraMap R R')).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K) a t
          (bcTmul.{uR, uRp, max v uR uA uRp} (algebraMap R R') 1 k))) =
      w6.{uR, uA, uRp, v} K a t k :=
  chainIdentity_piece₄ K a t k

/-- The hypothesis of `Dualizing.chainIdentity_aux` on the pure tensors `Dualizing.tmulBC`. -/
theorem he_tmulBC (K : CochainComplex (ModuleCat.{max v uR uA uRp} R) ℤ)
    (e : HomologicalComplex.mapBifunctor
        (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
            (algebraMap R R')).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K)
        (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
            (algebraMap R R')).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P)
        (moduleTensor.{uRp, max (max v uR) uRp (max uA uRp)} R') (ComplexShape.up ℤ) ≅
      ((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp} (algebraMap R R')).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
        (HomologicalComplex.mapBifunctor K P (moduleTensor.{uR, max (max v uRp) uR uA} R)
          (ComplexShape.up ℤ)))
    (he : ∀ (a b n : ℤ) (hab : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (a, b)
        = n)
      (k : K.X a) (z : P.X b),
      (e.hom.f n).hom ((HomologicalComplex.ιMapBifunctor
          (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
              (algebraMap R R')).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K)
          (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
              (algebraMap R R')).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P)
          (moduleTensor.{uRp, max (max v uR) uRp (max uA uRp)} R') (ComplexShape.up ℤ) a b
              n hab).hom
        ((bcTmulC.{uR, uRp, max v uR uA uRp} (algebraMap R R') K a 1 k) ⊗ₜ[R']
          (bcTmulC.{uR, uRp, max v uR uA uRp} (algebraMap R R') P b 1 z))) =
      bcTmulC.{uR, uRp, max v uR uA uRp} (algebraMap R R')
        (HomologicalComplex.mapBifunctor K P (moduleTensor.{uR, max (max v uRp) uR uA} R)
          (ComplexShape.up ℤ)) n 1
        ((HomologicalComplex.ιMapBifunctor K P (moduleTensor.{uR, max (max v uRp) uR uA} R)
          (ComplexShape.up ℤ) a b n hab).hom (k ⊗ₜ[R] z)))
    (a b n : ℤ) (hab : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (a, b) = n)
    (k : K.X a) (z : P.X b) :
    (e.hom.f n).hom ((HomologicalComplex.ιMapBifunctor
        (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
        (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
        (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
        (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
        (moduleTensor.{uRp, max (max v uR) uRp (max uA uRp)} R')
        (ComplexShape.up ℤ) a b n hab).hom (tmulBC.{uR, uA, uRp, v} K P a b k z)) =
      bcTmulC.{uR, uRp, max v uR uA uRp} (algebraMap R R')
        (HomologicalComplex.mapBifunctor K P (moduleTensor.{uR, max (max v uRp) uR uA} R)
            (ComplexShape.up ℤ)) n 1
        ((HomologicalComplex.ιMapBifunctor K P (moduleTensor.{uR, max (max v uRp) uR uA} R)
            (ComplexShape.up ℤ) a b n hab).hom (k ⊗ₜ[R] z)) :=
  he a b n hab k z

/-- `Dualizing.chainIdentity_rhs` on the pure tensor `Dualizing.tmulBC`, with value
`Dualizing.w6`. -/
theorem chainIdentity_rhs_tmulBC (K : CochainComplex (ModuleCat.{max v uR uA uRp} R) ℤ) (a : ℤ)
    (hab : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (a, 0) = a)
    (k : K.X a) (z : P.X 0) :
    (HomologicalComplex.ιMapBifunctor (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
        (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
        (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
        (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
        (moduleTensor.{uRp, max (max v uR) uRp (max uA uRp)} R') (ComplexShape.up ℤ) a 0 a hab ≫
        (HomologicalComplex.mapBifunctorMap (𝟙 _)
          (baseChangeResolution.{uR, uA, uRp, v} baseChangeR comparisonR baseChangeA comparisonA
              P p)
          (moduleTensor.{uRp, max (max v uR) uRp (max uA uRp)} R') (ComplexShape.up ℤ)).f a).hom
              (tmulBC.{uR, uA, uRp, v} K P a 0 k z) =
      w6.{uR, uA, uRp, v} K a (algebraMap A (TensorProduct R A R')
          ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          (algebraModule.{max v uRp} (algebraMap R A))).hom.hom ((p.f 0).hom z)).down) k :=
  chainIdentity_rhs baseChangeR comparisonR baseChangeA comparisonA P p K a hab k z

/-- Five composable maps out of the tensor product of two base changes agree with a sixth as
soon as they agree on the pure tensors `Dualizing.tmulBC` of every summand. -/
theorem comp₅_hom_ext_tmulBC (K P : CochainComplex (ModuleCat.{max v uR uA uRp} R) ℤ)
    {X₂ X₃ X₄ X₅ Z : HomologicalComplex (ModuleCat.{max v uR uA uRp} R') (ComplexShape.up ℤ)}
    (φ₁ : HomologicalComplex.mapBifunctor
        (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
        (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
        (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
        (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
        (moduleTensor.{uRp, max (max v uR) uRp (max uA uRp)} R')
      (ComplexShape.up ℤ) ⟶ X₂) (φ₂ : X₂ ⟶ X₃) (φ₃ : X₃ ⟶ X₄) (φ₄ : X₄ ⟶ X₅) (φ₅ : X₅ ⟶ Z)
    (ψ : HomologicalComplex.mapBifunctor
        (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
        (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
        (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
        (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
        (moduleTensor.{uRp, max (max v uR) uRp (max uA uRp)} R')
      (ComplexShape.up ℤ) ⟶ Z)
    (h : ∀ (a b n : ℤ) (hab : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (a, b)
        = n)
      (k : K.X a) (z : P.X b),
      (φ₅.f n).hom ((φ₄.f n).hom ((φ₃.f n).hom ((φ₂.f n).hom ((φ₁.f n).hom
        ((HomologicalComplex.ιMapBifunctor
            (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
            (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
            (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
            (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
            (moduleTensor.{uRp, max (max v uR) uRp (max uA uRp)} R')
          (ComplexShape.up ℤ) a b n hab).hom (tmulBC.{uR, uA, uRp, v} K P a b k z)))))) =
      (ψ.f n).hom ((HomologicalComplex.ιMapBifunctor
          (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
          (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
          (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
          (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
          (moduleTensor.{uRp, max (max v uR) uRp (max uA uRp)} R')
          (ComplexShape.up ℤ) a b n hab).hom (tmulBC.{uR, uA, uRp, v} K P a b k z))) :
    φ₁ ≫ φ₂ ≫ φ₃ ≫ φ₄ ≫ φ₅ = ψ := by
  ext n : 1
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro a b hab
  exact extendScalars_tensor_hom_ext_tmulBC.{uR, uA, uRp, v} K P a b _ _
    fun k z => h a b n hab k z

/-- A map of complexes of `R'`-modules on an element of a degree, with all universe levels
spelled `max v uR uA uRp`. -/
def evalB {X Y : HomologicalComplex (ModuleCat.{max v uR uA uRp} R') (ComplexShape.up ℤ)}
    (φ : X ⟶ Y) (n : ℤ) (x : X.X n) : Y.X n :=
  (φ.f n).hom x

/-- `Dualizing.comp₅_hom_ext_tmulBC` read through `Dualizing.evalB`. -/
theorem comp₅_hom_ext_evalB (K P : CochainComplex (ModuleCat.{max v uR uA uRp} R) ℤ)
    {X₂ X₃ X₄ X₅ Z : HomologicalComplex (ModuleCat.{max v uR uA uRp} R') (ComplexShape.up ℤ)}
    (φ₁ : HomologicalComplex.mapBifunctor
        (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
        (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
        (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
        (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
        (moduleTensor.{uRp, max (max v uR) uRp (max uA uRp)} R')
      (ComplexShape.up ℤ) ⟶ X₂) (φ₂ : X₂ ⟶ X₃) (φ₃ : X₃ ⟶ X₄) (φ₄ : X₄ ⟶ X₅) (φ₅ : X₅ ⟶ Z)
    (ψ : HomologicalComplex.mapBifunctor
        (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
        (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
        (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
        (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
        (moduleTensor.{uRp, max (max v uR) uRp (max uA uRp)} R')
      (ComplexShape.up ℤ) ⟶ Z)
    (h : ∀ (a b n : ℤ) (hab : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (a, b)
        = n)
      (k : K.X a) (z : P.X b),
      evalB.{uR, uA, uRp, v} φ₅ n (evalB.{uR, uA, uRp, v} φ₄ n
          (evalB.{uR, uA, uRp, v} φ₃ n (evalB.{uR, uA, uRp, v} φ₂ n (evalB.{uR, uA, uRp, v} φ₁ n
        ((HomologicalComplex.ιMapBifunctor
            (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
            (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
            (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
            (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
            (moduleTensor.{uRp, max (max v uR) uRp (max uA uRp)} R')
          (ComplexShape.up ℤ) a b n hab).hom (tmulBC.{uR, uA, uRp, v} K P a b k z)))))) =
      evalB.{uR, uA, uRp, v} ψ n ((HomologicalComplex.ιMapBifunctor
          (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
          (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
          (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
          (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
          (moduleTensor.{uRp, max (max v uR) uRp (max uA uRp)} R')
          (ComplexShape.up ℤ) a b n hab).hom (tmulBC.{uR, uA, uRp, v} K P a b k z))) :
    φ₁ ≫ φ₂ ≫ φ₃ ≫ φ₄ ≫ φ₅ = ψ :=
  comp₅_hom_ext_tmulBC.{uR, uA, uRp, v} K P φ₁ φ₂ φ₃ φ₄ φ₅ ψ h

/-- `Dualizing.chainIdentity_piece₁'` read through `Dualizing.evalB`. -/
theorem chainIdentity_evalB_piece₁ (K : CochainComplex (ModuleCat.{max v uR uA uRp} R) ℤ) (a : ℤ)
    (hab : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (a, 0) = a)
    (k : K.X a) (z : P.X 0) : evalB.{uR, uA, uRp, v}
        (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
        (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (HomologicalComplex.mapBifunctorMap (𝟙 K) p (moduleTensor.{uR, max (max v uRp) uR uA} R)
        (ComplexShape.up ℤ) ≫ (extendRestrictComplexIso.{max v uRp} (algebraMap R A) K).inv)) a
        (bcTmulC.{uR, uRp, max v uR uA uRp} (algebraMap R R')
        (HomologicalComplex.mapBifunctor K P (moduleTensor.{uR, max (max v uRp) uR uA} R)
        (ComplexShape.up ℤ)) a 1 ((HomologicalComplex.ιMapBifunctor K P
        (moduleTensor.{uR, max (max v uRp) uR uA} R) (ComplexShape.up ℤ) a 0 a hab).hom
        (k ⊗ₜ[R] z))) = (bcTmulC.{uR, uRp, max v uR uA uRp} (algebraMap R R')
        (((ModuleCat.restrictScalars.{max v uR uA uRp} (algebraMap R A)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp}
        (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) a 1
        (resC.{uR, uA, max v uR uA uRp} (algebraMap R A)
        (((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp} (algebraMap R A)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K) a (bcTmul.{uR, uA, max v uR uA uRp} (algebraMap R A)
        ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (algebraModule.{max v uRp} (algebraMap R A))).hom.hom ((p.f 0).hom z)).down k))) :=
  chainIdentity_piece₁' P p K a hab k z

/-- `Dualizing.chainIdentity_piece₂'` read through `Dualizing.evalB`. -/
theorem chainIdentity_evalB_piece₂ (K : CochainComplex (ModuleCat.{max v uR uA uRp} R) ℤ) (a : ℤ)
    (hab : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (a, 0) = a)
    (k : K.X a) (z : P.X 0) : evalB.{uR, uA, uRp, v}
        (chainBaseChangeComparison.{uR, uA, uRp, v} baseChangeR comparisonR baseChangeA comparisonA
        (((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp} (algebraMap R A)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K)) a (bcTmulC.{uR, uRp, max v uR uA uRp} (algebraMap R R')
        (((ModuleCat.restrictScalars.{max v uR uA uRp} (algebraMap R A)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp}
        (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) a 1
        (resC.{uR, uA, max v uR uA uRp} (algebraMap R A)
        (((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp} (algebraMap R A)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K) a (bcTmul.{uR, uA, max v uR uA uRp} (algebraMap R A)
        ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (algebraModule.{max v uRp} (algebraMap R A))).hom.hom ((p.f 0).hom z)).down k))) =
        (resC.{uRp, max uA uRp, max v uR uA uRp}
        (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R A R').toRingHom
        (((ModuleCat.extendScalars.{uA, max uA uRp, max v uR uA uRp}
        (algebraMap A (TensorProduct R A R'))).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp} (algebraMap R A)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K)) a (bcTmulC.{uA, max uA uRp, max v uR uA uRp}
        (algebraMap A (TensorProduct R A R'))
        (((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp} (algebraMap R A)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K) a 1 (bcTmul.{uR, uA, max v uR uA uRp} (algebraMap R A)
        ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (algebraModule.{max v uRp} (algebraMap R A))).hom.hom ((p.f 0).hom z)).down k))) :=
  chainIdentity_piece₂' baseChangeR comparisonR baseChangeA comparisonA K a
      ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
      (algebraModule.{max v uRp} (algebraMap R A))).hom.hom ((p.f 0).hom z)).down k

/-- `Dualizing.chainIdentity_piece₃'` read through `Dualizing.evalB`. -/
theorem chainIdentity_evalB_piece₃ (K : CochainComplex (ModuleCat.{max v uR uA uRp} R) ℤ) (a : ℤ)
    (hab : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (a, 0) = a)
    (k : K.X a) (z : P.X 0) : evalB.{uR, uA, uRp, v}
        (((ModuleCat.restrictScalars.{max v uR uA uRp}
        (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R
        A R').toRingHom).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (chainExtendScalarsSwap.{uR, uA, uRp, v} K)) a
        (resC.{uRp, max uA uRp, max v uR uA uRp}
        (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R A R').toRingHom
        (((ModuleCat.extendScalars.{uA, max uA uRp, max v uR uA uRp}
        (algebraMap A (TensorProduct R A R'))).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp} (algebraMap R A)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K)) a (bcTmulC.{uA, max uA uRp, max v uR uA uRp}
        (algebraMap A (TensorProduct R A R'))
        (((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp} (algebraMap R A)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K) a 1 (bcTmul.{uR, uA, max v uR uA uRp} (algebraMap R A)
        ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (algebraModule.{max v uRp} (algebraMap R A))).hom.hom ((p.f 0).hom z)).down k))) =
        (resC.{uRp, max uA uRp, max v uR uA uRp}
        (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R A R').toRingHom
        (((ModuleCat.extendScalars.{uRp, max uA uRp, max v uR uA uRp}
        (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R
        A R').toRingHom).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
        (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) a
        (bcTmulC.{uRp, max uA uRp, max v uR uA uRp}
        (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R A R').toRingHom
        (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
        (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) a
        (algebraMap A (TensorProduct R A R')
        ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (algebraModule.{max v uRp} (algebraMap R A))).hom.hom ((p.f 0).hom z)).down)
        (bcTmul.{uR, uRp, max v uR uA uRp} (algebraMap R R') 1 k))) :=
  chainIdentity_piece₃' K a ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
      (algebraModule.{max v uRp} (algebraMap R A))).hom.hom ((p.f 0).hom z)).down k

/-- `Dualizing.chainIdentity_piece₄'` read through `Dualizing.evalB`. -/
theorem chainIdentity_evalB_piece₄ (K : CochainComplex (ModuleCat.{max v uR uA uRp} R) ℤ) (a : ℤ)
    (hab : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (a, 0) = a)
    (k : K.X a) (z : P.X 0) : evalB.{uR, uA, uRp, v}
        (extendRestrictComplexIso.{max v uR}
        (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R A R').toRingHom
        (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
        (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)).hom a
        (resC.{uRp, max uA uRp, max v uR uA uRp}
        (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R A R').toRingHom
        (((ModuleCat.extendScalars.{uRp, max uA uRp, max v uR uA uRp}
        (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R
        A R').toRingHom).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
        (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) a
        (bcTmulC.{uRp, max uA uRp, max v uR uA uRp}
        (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R A R').toRingHom
        (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
        (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) a
        (algebraMap A (TensorProduct R A R')
        ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (algebraModule.{max v uRp} (algebraMap R A))).hom.hom ((p.f 0).hom z)).down)
        (bcTmul.{uR, uRp, max v uR uA uRp} (algebraMap R R') 1 k))) =
        (w6.{uR, uA, uRp, v} K a (algebraMap A (TensorProduct R A R')
        ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (algebraModule.{max v uRp} (algebraMap R A))).hom.hom ((p.f 0).hom z)).down) k) :=
  chainIdentity_piece₄' K a (algebraMap A (TensorProduct R A R')
      ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
      (algebraModule.{max v uRp} (algebraMap R A))).hom.hom ((p.f 0).hom z)).down) k

/-- `Dualizing.chainIdentity_rhs_tmulBC` read through `Dualizing.evalB`. -/
theorem chainIdentity_evalB_rhs (K : CochainComplex (ModuleCat.{max v uR uA uRp} R) ℤ) (a : ℤ)
    (hab : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (a, 0) = a)
    (k : K.X a) (z : P.X 0) : evalB.{uR, uA, uRp, v}
        (HomologicalComplex.mapBifunctorMap (𝟙 _)
        (baseChangeResolution.{uR, uA, uRp, v} baseChangeR comparisonR baseChangeA comparisonA P p)
        (moduleTensor.{uRp, max (max v uR) uRp (max uA uRp)} R') (ComplexShape.up ℤ)) a
        ((HomologicalComplex.ιMapBifunctor
        (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
        (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
        (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
        (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
        (moduleTensor.{uRp, max (max v uR) uRp (max uA uRp)} R') (ComplexShape.up ℤ) a 0 a hab).hom
        (tmulBC.{uR, uA, uRp, v} K P a 0 k z)) =
        (w6.{uR, uA, uRp, v} K a (algebraMap A (TensorProduct R A R')
        ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (algebraModule.{max v uRp} (algebraMap R A))).hom.hom ((p.f 0).hom z)).down) k) :=
  chainIdentity_rhs_tmulBC baseChangeR comparisonR baseChangeA comparisonA P p K a hab k z

/-- `Dualizing.evalB` vanishes on zero. -/
theorem evalB_zero {X Y : HomologicalComplex (ModuleCat.{max v uR uA uRp} R') (ComplexShape.up ℤ)}
    (φ : X ⟶ Y) (n : ℤ) : evalB.{uR, uA, uRp, v} φ n 0 = 0 :=
  map_zero _

/-- Three further maps after one that kills an element still kill it. -/
theorem evalB₃_zero {X₃ X₄ X₅ Z : HomologicalComplex (ModuleCat.{max v uR uA uRp} R')
    (ComplexShape.up ℤ)} {X₂ : HomologicalComplex (ModuleCat.{max v uR uA uRp} R')
    (ComplexShape.up ℤ)} (φ₂ : X₂ ⟶ X₃) (φ₃ : X₃ ⟶ X₄)
    (φ₄ : X₄ ⟶ X₅) (φ₅ : X₅ ⟶ Z) (n : ℤ) (x : X₂.X n) (hx : evalB.{uR, uA, uRp, v} φ₂ n x = 0) :
    evalB.{uR, uA, uRp, v} φ₅ n (evalB.{uR, uA, uRp, v} φ₄ n (evalB.{uR, uA, uRp, v} φ₃ n
      (evalB.{uR, uA, uRp, v} φ₂ n x))) = 0 := by
  rw [hx, evalB_zero, evalB_zero, evalB_zero]

/-- Applying `Dualizing.evalB` of a map to an equation, then continuing with a second equation. -/
private theorem evalB_eq_trans {X Y : HomologicalComplex (ModuleCat.{max v uR uA uRp} R')
    (ComplexShape.up ℤ)} {n : ℤ} {x x' : X.X n} {y : Y.X n} (φ : X ⟶ Y) (h : x = x')
    (h' : evalB.{uR, uA, uRp, v} φ n x' = y) : evalB.{uR, uA, uRp, v} φ n x = y :=
  h ▸ h'

/-- The pure tensor `t ⊗ 0` vanishes. -/
theorem bcTmulC_zero {S : Type uR} {T : Type uA} [CommRing S] [CommRing T] (f : S →+* T)
    (X : CochainComplex (ModuleCat.{v} S) ℤ) (i : ℤ) (t : T) :
    bcTmulC.{uR, uA, v} f X i t 0 = 0 :=
  TensorProduct.tmul_zero _ _

/-- The tensor base-change isomorphism on `Dualizing.tmulBC`, read through `Dualizing.evalB`. -/
theorem chainIdentity_evalB_tensor (K : CochainComplex (ModuleCat.{max v uR uA uRp} R) ℤ)
    (e : HomologicalComplex.mapBifunctor
        (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
            (algebraMap R R')).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K)
        (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
            (algebraMap R R')).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P)
        (moduleTensor.{uRp, max (max v uR) uRp (max uA uRp)} R') (ComplexShape.up ℤ) ≅
      ((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp} (algebraMap R R')).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
        (HomologicalComplex.mapBifunctor K P (moduleTensor.{uR, max (max v uRp) uR uA} R)
          (ComplexShape.up ℤ)))
    (he : ∀ (a b n : ℤ) (hab : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (a, b)
        = n)
      (k : K.X a) (z : P.X b),
      (e.hom.f n).hom ((HomologicalComplex.ιMapBifunctor
          (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
              (algebraMap R R')).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K)
          (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
              (algebraMap R R')).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P)
          (moduleTensor.{uRp, max (max v uR) uRp (max uA uRp)} R') (ComplexShape.up ℤ) a b
              n hab).hom
        ((bcTmulC.{uR, uRp, max v uR uA uRp} (algebraMap R R') K a 1 k) ⊗ₜ[R']
          (bcTmulC.{uR, uRp, max v uR uA uRp} (algebraMap R R') P b 1 z))) =
      bcTmulC.{uR, uRp, max v uR uA uRp} (algebraMap R R')
        (HomologicalComplex.mapBifunctor K P (moduleTensor.{uR, max (max v uRp) uR uA} R)
          (ComplexShape.up ℤ)) n 1
        ((HomologicalComplex.ιMapBifunctor K P (moduleTensor.{uR, max (max v uRp) uR uA} R)
          (ComplexShape.up ℤ) a b n hab).hom (k ⊗ₜ[R] z)))
(a b n : ℤ)
    (hab : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (a, b) = n)
    (k : K.X a) (z : P.X b) :
    evalB.{uR, uA, uRp, v} e.hom n ((HomologicalComplex.ιMapBifunctor
        (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
        (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
        (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
        (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
        (moduleTensor.{uRp, max (max v uR) uRp (max uA uRp)} R') (ComplexShape.up ℤ) a b n hab).hom
        (tmulBC.{uR, uA, uRp, v} K P a b k z)) =
        (bcTmulC.{uR, uRp, max v uR uA uRp} (algebraMap R R')
        (HomologicalComplex.mapBifunctor K P (moduleTensor.{uR, max (max v uRp) uR uA} R)
        (ComplexShape.up ℤ)) n 1 ((HomologicalComplex.ιMapBifunctor K P
        (moduleTensor.{uR, max (max v uRp) uR uA} R) (ComplexShape.up ℤ) a b n hab).hom
        (k ⊗ₜ[R] z))) :=
  he_tmulBC P K e he a b n hab k z

/-- On the summand of bidegree `(a, b)` with `b ≠ 0`, the first map of the chain identity kills
the base change of every pure tensor. -/
theorem chainIdentity_evalB_piece₁_of_ne_zero (K : CochainComplex (ModuleCat.{max v uR uA uRp} R) ℤ)
    (a b n : ℤ)
    (hab : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (a, b) = n)
    (hb : b ≠ 0) (k : K.X a) (z : P.X b) : evalB.{uR, uA, uRp, v}
        (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
        (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (HomologicalComplex.mapBifunctorMap (𝟙 K) p (moduleTensor.{uR, max (max v uRp) uR uA} R)
        (ComplexShape.up ℤ) ≫ (extendRestrictComplexIso.{max v uRp} (algebraMap R A) K).inv)) n
        (bcTmulC.{uR, uRp, max v uR uA uRp} (algebraMap R R')
        (HomologicalComplex.mapBifunctor K P (moduleTensor.{uR, max (max v uRp) uR uA} R)
        (ComplexShape.up ℤ)) n 1 ((HomologicalComplex.ιMapBifunctor K P
        (moduleTensor.{uR, max (max v uRp) uR uA} R) (ComplexShape.up ℤ) a b n hab).hom
        (k ⊗ₜ[R] z))) = 0 := by
  have h0 := mapBifunctorMap_f_ι_tmul_eq_zero_of_single.{uR, max (max v uRp) uR uA} K p a b n hab hb
      k z
  have h1 : ((((extendRestrictComplexIso.{max v uRp} (algebraMap R A) K).inv).f n).hom
      (((HomologicalComplex.mapBifunctorMap (𝟙 K) p (moduleTensor.{uR, max (max v uRp) uR uA} R)
          (ComplexShape.up ℤ)).f n).hom
        ((HomologicalComplex.ιMapBifunctor K P (moduleTensor.{uR, max (max v uRp) uR uA} R)
            (ComplexShape.up ℤ) a b n hab).hom
          (k ⊗ₜ[R] z)))) = 0 := by
    rw [h0, map_zero]
  exact (congrArg (bcTmulC.{uR, uRp, max v uR uA uRp} (algebraMap R R') _ n 1) h1).trans
      (bcTmulC_zero _ _ n 1)

/-- On the summand of bidegree `(a, b)` with `b ≠ 0`, the right side of the chain identity
kills every pure tensor. -/
theorem chainIdentity_evalB_rhs_of_ne_zero (K : CochainComplex (ModuleCat.{max v uR uA uRp} R) ℤ)
    (a b n : ℤ)
    (hab : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (a, b) = n)
    (hb : b ≠ 0) (k : K.X a) (z : P.X b) : evalB.{uR, uA, uRp, v}
        (HomologicalComplex.mapBifunctorMap (𝟙 _)
        (baseChangeResolution.{uR, uA, uRp, v} baseChangeR comparisonR baseChangeA comparisonA P p)
        (moduleTensor.{uRp, max (max v uR) uRp (max uA uRp)} R') (ComplexShape.up ℤ)) n
        ((HomologicalComplex.ιMapBifunctor
        (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
        (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
        (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
        (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
        (moduleTensor.{uRp, max (max v uR) uRp (max uA uRp)} R') (ComplexShape.up ℤ) a b n hab).hom
        (tmulBC.{uR, uA, uRp, v} K P a b k z)) = 0 :=
  mapBifunctorMap_f_ι_tmul_eq_zero_of_single.{uRp, max (max v uR) uRp (max uA uRp)}
      (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp} (algebraMap R R')).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K)
    (baseChangeResolution.{uR, uA, uRp, v} baseChangeR comparisonR baseChangeA comparisonA P p)
    a b n hab hb _ _

/-- `Dualizing.chainIdentity` with every tensor product spelled at one universe argument, and the
tensor base-change isomorphism given on pure tensors. -/
theorem chainIdentity_aux (K : CochainComplex (ModuleCat.{max v uR uA uRp} R) ℤ)
    (e : HomologicalComplex.mapBifunctor
        (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
            (algebraMap R R')).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K)
        (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
            (algebraMap R R')).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P)
        (moduleTensor.{uRp, max (max v uR) uRp (max uA uRp)} R') (ComplexShape.up ℤ) ≅
      ((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp} (algebraMap R R')).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
        (HomologicalComplex.mapBifunctor K P (moduleTensor.{uR, max (max v uRp) uR uA} R)
          (ComplexShape.up ℤ)))
    (he : ∀ (a b n : ℤ) (hab : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (a, b)
        = n)
      (k : K.X a) (z : P.X b),
      (e.hom.f n).hom ((HomologicalComplex.ιMapBifunctor
          (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
              (algebraMap R R')).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K)
          (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
              (algebraMap R R')).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P)
          (moduleTensor.{uRp, max (max v uR) uRp (max uA uRp)} R') (ComplexShape.up ℤ) a b
              n hab).hom
        ((bcTmulC.{uR, uRp, max v uR uA uRp} (algebraMap R R') K a 1 k) ⊗ₜ[R']
          (bcTmulC.{uR, uRp, max v uR uA uRp} (algebraMap R R') P b 1 z))) =
      bcTmulC.{uR, uRp, max v uR uA uRp} (algebraMap R R')
        (HomologicalComplex.mapBifunctor K P (moduleTensor.{uR, max (max v uRp) uR uA} R)
          (ComplexShape.up ℤ)) n 1
        ((HomologicalComplex.ιMapBifunctor K P (moduleTensor.{uR, max (max v uRp) uR uA} R)
          (ComplexShape.up ℤ) a b n hab).hom (k ⊗ₜ[R] z))) :
    e.hom ≫
      ((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp} (algebraMap R R')).mapHomologicalComplex
          (ComplexShape.up ℤ)).map
        (HomologicalComplex.mapBifunctorMap (𝟙 K) p (moduleTensor.{uR, max (max v uRp) uR uA} R)
          (ComplexShape.up ℤ) ≫ (extendRestrictComplexIso.{max v uRp} (algebraMap R A) K).inv) ≫
      chainBaseChangeComparison.{uR, uA, uRp, v} baseChangeR comparisonR baseChangeA comparisonA
        (((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp} (algebraMap R A)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K) ≫
      ((ModuleCat.restrictScalars.{max v uR uA uRp}
          (Algebra.TensorProduct.includeRight :
            R' →ₐ[R] TensorProduct R A R').toRingHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (chainExtendScalarsSwap.{uR, uA, uRp, v} K) ≫
      (extendRestrictComplexIso.{max v uR}
        (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R A R').toRingHom
        (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
          (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)).hom =
    HomologicalComplex.mapBifunctorMap (𝟙 _)
      (baseChangeResolution.{uR, uA, uRp, v} baseChangeR comparisonR baseChangeA comparisonA P p)
      (moduleTensor.{uRp, max (max v uR) uRp (max uA uRp)} R') (ComplexShape.up ℤ) := by
  refine comp₅_hom_ext_evalB.{uR, uA, uRp, v} K P _ _ _ _ _ _ fun a b n hab k z => ?_
  by_cases hb : b = 0
  swap
  · have h₂ := chainIdentity_evalB_tensor.{uR, uA, uRp, v} P K e he a b n hab k z
    have h₃ := chainIdentity_evalB_piece₁_of_ne_zero.{uR, uA, uRp, v} (R' := R') P p K a b n hab hb
        k z
    exact (evalB₃_zero _ _ _ _ n _ (evalB_eq_trans _ h₂ h₃)).trans
      (chainIdentity_evalB_rhs_of_ne_zero.{uR, uA, uRp, v} baseChangeR comparisonR baseChangeA
          comparisonA P p K a b n hab hb k z).symm
  subst hb
  obtain rfl : a = n := by
    rw [← hab]
    exact (add_zero a).symm
  -- the element `1 ⊗ (k ⊗ z)` after the tensor base-change isomorphism
  have h₂ := chainIdentity_evalB_tensor.{uR, uA, uRp, v} P K e he a 0 a hab k z
  have h₃ := chainIdentity_evalB_piece₁.{uR, uA, uRp, v} (R' := R') P p K a hab k z
  have h₄ := chainIdentity_evalB_piece₂.{uR, uA, uRp, v} baseChangeR comparisonR baseChangeA
      comparisonA P p K a hab k z
  have h₅ := chainIdentity_evalB_piece₃.{uR, uA, uRp, v} (R' := R') P p K a hab k z
  have h₆ := chainIdentity_evalB_piece₄.{uR, uA, uRp, v} (R' := R') P p K a hab k z
  have hr := chainIdentity_evalB_rhs.{uR, uA, uRp, v} baseChangeR comparisonR baseChangeA
      comparisonA P p K a hab k z
  exact (evalB_eq_trans _ (evalB_eq_trans _ (evalB_eq_trans _ (evalB_eq_trans _ h₂ h₃) h₄) h₅)
    h₆).trans hr.symm

/-- **The chain-level identity behind [stacks 0E2A].** -/
theorem chainIdentity (K : CochainComplex (ModuleCat.{max v uR uA uRp} R) ℤ)
    (e : tensorComplex.{uRp, max uR (max v uA)}
        ((extensionOfScalarsCochain.{uR, uRp, max v uA} (algebraMap R R')).obj K)
        ((extensionOfScalarsCochain.{uR, uRp, max v uA} (algebraMap R R')).obj P) ≅
      (extensionOfScalarsCochain.{uR, uRp, max v uA} (algebraMap R R')).obj
        (tensorComplex.{uR, max uRp (max v uA)} K P))
    (he : IsTensorBaseChangeIso.{uR, uRp, max v uA} (algebraMap R R') K P e) :
    e.hom ≫
      ((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp} (algebraMap R R')).mapHomologicalComplex
          (ComplexShape.up ℤ)).map
        (HomologicalComplex.mapBifunctorMap (𝟙 K) p (moduleTensor.{uR, max v uR uA uRp} R)
          (ComplexShape.up ℤ) ≫ (extendRestrictComplexIso.{max v uRp} (algebraMap R A) K).inv) ≫
      (NatTrans.mapHomologicalComplex
        (RingTheory.TorIndependence.derivedBaseChangeComparison
          (algebraMap R A) (algebraMap R R')
          (algebraMap A (TensorProduct R A R')) (algebraMap R' (TensorProduct R A R'))
          ((IsScalarTower.algebraMap_eq R A (TensorProduct R A R')).symm.trans
            (IsScalarTower.algebraMap_eq R R' (TensorProduct R A R')))
          baseChangeR baseChangeA comparisonR comparisonA).1
        (ComplexShape.up ℤ)).app
        (((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp} (algebraMap R A)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K) ≫
      ((ModuleCat.restrictScalars.{max v uR uA uRp}
          (Algebra.TensorProduct.includeRight :
            R' →ₐ[R] TensorProduct R A R').toRingHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex
            (RingTheory.TorIndependence.extendScalarsCompInvOfEq.{uR, uA, max uA uRp, max v uRp}
                (algebraMap R A)
              (algebraMap A (TensorProduct R A R')) (algebraMap R (TensorProduct R A R'))
              algebraMap_tensorProduct_comp_left) (ComplexShape.up ℤ)).app K ≫
          ((NatIso.mapHomologicalComplex
            (extendScalarsCompIsoOfEq.{uR, uRp, max uA uRp, max v uA} (algebraMap R R')
              (Algebra.TensorProduct.includeRight :
                R' →ₐ[R] TensorProduct R A R').toRingHom
              (algebraMap R (TensorProduct R A R')) algebraMap_tensorProduct_comp_right)
            (ComplexShape.up ℤ)).app K).inv) ≫
      (extendRestrictComplexIso.{max v uR}
        (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R A R').toRingHom
        (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
          (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)).hom =
    HomologicalComplex.mapBifunctorMap (𝟙 _)
      (baseChangeResolution.{uR, uA, uRp, v} baseChangeR comparisonR baseChangeA comparisonA P p)
      (moduleTensor.{uRp, max (max v uR) uRp (max uA uRp)} R') (ComplexShape.up ℤ) :=
  chainIdentity_of_aux baseChangeR comparisonR baseChangeA comparisonA P p
    (fun K e he => chainIdentity_aux baseChangeR comparisonR baseChangeA comparisonA P p K e he)
    K e he

end Dualizing
