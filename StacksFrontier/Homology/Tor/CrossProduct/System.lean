module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Category.ModuleCat.LeftResolution
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Mathlib.Algebra.Homology.Embedding.ExtendHomotopy
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.RingTheory.TensorProduct.Maps
public import StacksFrontier.Algebra.Category.ModuleCat.Monoidal.LargeUniverse
public import StacksFrontier.Algebra.Homology.KFlat
public import StacksFrontier.Algebra.Homology.Resolution.ProjectiveResolution
public import StacksFrontier.Homology.KFlat.Flat
public import StacksFrontier.Homology.Tor.Products
public import StacksFrontier.Homology.Tor.BaseChangeTensorIso
public import StacksCore.Tactic.StacksAttribute

/-!
# Tor cross products: the specification

This file defines `Torⁿᴿ(-, A)` along a ring map `R → A`, the lifted cochain representatives
of nonnegatively graded chain complexes, the normalized comparison of lifted tensor complexes,
the cocycle-level product `ChainHomologyProduct` on homology and its agreement with Tag 068H,
and the structures `ResolutionModel` and `System` specifying a Tor cross product.
-/

open CategoryTheory CategoryTheory.Limits MonoidalCategory CochainComplex.DerivedTensor
open scoped TensorProduct

universe uR uA v w x

@[expose] public noncomputable section

namespace TorCrossProduct

attribute [local instance] HasDerivedCategory.standard

variable (R : Type uR) (A : Type uA) [CommRing R] [CommRing A]

/-- Extension of scalars along `f` is an additive functor, being a left adjoint. -/
public noncomputable instance (f : R →+* A) :
    (extensionScalars.{uR, uA, v} f).Additive := by
  let : (ModuleCat.extendScalars.{uR, uA, max uR uA v}
      f).IsLeftAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{max uR v, uR, uA} f).isLeftAdjoint
  exact CategoryTheory.rightExactFunctor_le_additiveFunctor _ _ _
    (by change PreservesFiniteColimits _; infer_instance)

/-- `Torⁿᴿ(-, A)` as an `A`-module-valued functor, with independent ring and module
universes. -/
public noncomputable abbrev torBaseChange (f : R →+* A) (n : ℕ) :
    ModuleCat.{max uR uA v} R ⥤ ModuleCat.{max uR uA v} A :=
  (extensionScalars.{uR, uA, v} f).leftDerived n

/-- The ordinary base-change comparison
`(A ⊗[R] M) ⊗[A] (A ⊗[R] N) → A ⊗[R] (M ⊗[R] N)` in the common module
universe. -/
public noncomputable def zeroBaseChange (f : R →+* A)
    (M N : ModuleCat.{max uR uA v} R) :
    ((ModuleCat.moduleTensorLarge.{uA, max uR v} A).obj
      ((extensionScalars f).obj M)).obj ((extensionScalars f).obj N) ⟶
      (extensionScalars f).obj
        (((ModuleCat.moduleTensorLarge.{uR, max uA v} R).obj M).obj N) := by
  letI := f.toAlgebra
  exact (TensorProduct.AlgebraTensorModule.distribBaseChange
    R A M N).symm.toModuleIso.hom

set_option linter.checkUnivs false in
/-- Tensoring two maps in module categories whose carrier universe is independent of the
ring universe. -/
public def moduleTensorMap {S : Type uA} [CommRing S]
    {M M' N N' : ModuleCat.{max uR uA v} S} (f : M ⟶ M') (g : N ⟶ N') :
    ((ModuleCat.moduleTensorLarge.{uA, max uR v} S).obj M).obj N ⟶
      ((ModuleCat.moduleTensorLarge.{uA, max uR v} S).obj M').obj N' :=
  ((ModuleCat.moduleTensorLarge.{uA, max uR v} S).map f).app N ≫
    ((ModuleCat.moduleTensorLarge.{uA, max uR v} S).obj M').map g

set_option linter.checkUnivs false in
/-- The total tensor product of two nonnegatively graded chain complexes, in an independent
module universe. -/
@[sga "7 VII 3.6" "special case"]
public noncomputable abbrev chainTensor {S : Type uA} [CommRing S]
    (K L : ChainComplex (ModuleCat.{max uR uA v} S) ℕ) :
    ChainComplex (ModuleCat.{max uR uA v} S) ℕ :=
  HomologicalComplex.mapBifunctor K L
    (ModuleCat.moduleTensorLarge.{uA, max uR v} S) (ComplexShape.down ℕ)

set_option linter.checkUnivs false in
/-- A nonnegatively graded chain complex of `A`-modules, regarded canonically as a complex of
modules over a universe lift of `A` and placed in nonpositive cohomological degrees.  This is the
representative used to compare the chain construction with Tag 068H. -/
public noncomputable def liftedCochain
    (K : ChainComplex (ModuleCat.{max uR uA v} A) ℕ) :
    CochainComplex (ModuleCat (ULift.{max uR v} A)) ℤ :=
  (ComplexShape.embeddingDownNat.extendFunctor
      (ModuleCat (ULift.{max uR v} A))).obj
    (((ModuleCat.restrictScalars
      (ULift.ringEquiv (R := A)).toRingHom).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj K)

set_option linter.checkUnivs false in
/-- Restriction along the ring equivalence from a universe lift of `A` to `A`. -/
public abbrev liftScalars : ModuleCat.{max uR uA v} A ⥤
    ModuleCat (ULift.{max uR v} A) :=
  ModuleCat.restrictScalars (ULift.ringEquiv (R := A)).toRingHom

/-- The termwise identification under restriction of scalars and extension by zero. -/
public abbrev liftedCochainXIso
    (K : ChainComplex (ModuleCat.{max uR uA v} A) ℕ)
    (n : ℕ) (i : ℤ) (h : -(n : ℤ) = i) :
    (liftedCochain.{uR, uA, v} A K).X i ≅
      (liftScalars.{uR, uA, v} A).obj (K.X n) :=
  (((liftScalars.{uR, uA, v} A).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj K).extendXIso ComplexShape.embeddingDownNat h

/-- The canonical homology identification for the universe lift and the reindexing `n ↦ -n`.
It is the composite of Mathlib's extension and scalar-restriction homology isomorphisms. -/
public abbrev liftedCochainHomologyIso
    (K : ChainComplex (ModuleCat.{max uR uA v} A) ℕ)
    (n : ℕ) (i : ℤ) (h : -(n : ℤ) = i) :
    (liftedCochain.{uR, uA, v} A K).homology i ≅
      (liftScalars.{uR, uA, v} A).obj (K.homology n) := by
  let e : ModuleCat.{max uR uA v} A ≌ ModuleCat (ULift.{max uR v} A) :=
    ModuleCat.restrictScalarsEquivalenceOfRingEquiv (ULift.ringEquiv (R := A))
  letI : (liftScalars.{uR, uA, v} A).IsLeftAdjoint := e.toAdjunction.isLeftAdjoint
  letI : (liftScalars.{uR, uA, v} A).IsRightAdjoint := e.symm.toAdjunction.isRightAdjoint
  exact (((liftScalars.{uR, uA, v} A).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj K).extendHomologyIso ComplexShape.embeddingDownNat h ≪≫
      (K.sc n).mapHomologyIso (liftScalars.{uR, uA, v} A)

/-- The tensor comparison for restriction along the universe-lift ring equivalence.
It sends a pure tensor to the same pure tensor over the original ring. -/
public abbrev liftScalarsTensorMap (M N : ModuleCat.{max uR uA v} A) :
    (liftScalars.{uR, uA, v} A).obj M ⊗ (liftScalars.{uR, uA, v} A).obj N ⟶
      (liftScalars.{uR, uA, v} A).obj
        (((ModuleCat.moduleTensorLarge.{uA, max uR v} A).obj M).obj N) := by
  letI : SMul (ULift.{max uR v} A) ((liftScalars.{uR, uA, v} A).obj M) :=
    ((liftScalars.{uR, uA, v} A).obj M).isModule.toSMul
  letI : SMul (ULift.{max uR v} A) ((liftScalars.{uR, uA, v} A).obj N) :=
    ((liftScalars.{uR, uA, v} A).obj N).isModule.toSMul
  letI : SMul (ULift.{max uR v} A)
      ((liftScalars.{uR, uA, v} A).obj
        (((ModuleCat.moduleTensorLarge.{uA, max uR v} A).obj M).obj N)) :=
    ((liftScalars.{uR, uA, v} A).obj
      (((ModuleCat.moduleTensorLarge.{uA, max uR v} A).obj M).obj N)).isModule.toSMul
  letI : SMulCommClass (ULift.{max uR v} A) (ULift.{max uR v} A)
      ((liftScalars.{uR, uA, v} A).obj
        (((ModuleCat.moduleTensorLarge.{uA, max uR v} A).obj M).obj N)) :=
    ⟨fun a b z ↦ smul_comm a.down b.down z⟩
  let b : (liftScalars.{uR, uA, v} A).obj M →ₗ[ULift.{max uR v} A]
      (liftScalars.{uR, uA, v} A).obj N →ₗ[ULift.{max uR v} A]
        (liftScalars.{uR, uA, v} A).obj
          (((ModuleCat.moduleTensorLarge.{uA, max uR v} A).obj M).obj N) :=
    { toFun := fun x ↦
        { toFun := fun y ↦ x ⊗ₜ[A] y
          map_add' := fun y z ↦ TensorProduct.tmul_add x y z
          map_smul' := fun r y ↦
            TensorProduct.tmul_smul (R := A) (M := M) (N := N) r.down x y }
      map_add' := fun x y ↦ by ext z; exact TensorProduct.add_tmul x y z
      map_smul' := fun r x ↦ by
        ext y
        exact (TensorProduct.smul_tmul' (R := A) (M := M) (N := N) r.down x y).symm }
  exact ModuleCat.ofHom
    (X := ((liftScalars.{uR, uA, v} A).obj M ⊗
      (liftScalars.{uR, uA, v} A).obj N : ModuleCat (ULift.{max uR v} A)))
    (Y := (liftScalars.{uR, uA, v} A).obj
      (((ModuleCat.moduleTensorLarge.{uA, max uR v} A).obj M).obj N))
    (TensorProduct.lift b)

/-- The canonical comparison between the tensor product of the lifted cochain complexes and
lifting the total chain tensor product, characterized on every homogeneous summand. -/
public structure LiftedTensorComparison
    (K L : ChainComplex (ModuleCat.{max uR uA v} A) ℕ) where
  /-- The comparison of total complexes. -/
  iso : liftedCochain.{uR, uA, v} A K ⊗ liftedCochain.{uR, uA, v} A L ≅
    liftedCochain.{uR, uA, v} A (chainTensor.{uR, uA, v} K L)
  /-- The comparison sends each homogeneous pure tensor to that same tensor in the total
  complex; this specifies the comparison, including its sign. -/
  ι_hom (p q k : ℕ) (h : p + q = k) :
    HomologicalComplex.ιTensorObj
        (liftedCochain.{uR, uA, v} A K) (liftedCochain.{uR, uA, v} A L)
        (-(p : ℤ)) (-(q : ℤ)) (-(k : ℤ)) (by omega) ≫
        iso.hom.f (-(k : ℤ)) ≫
        (liftedCochainXIso.{uR, uA, v} A (chainTensor.{uR, uA, v} K L) k (-(k : ℤ)) rfl).hom =
      ((liftedCochainXIso.{uR, uA, v} A K p (-(p : ℤ)) rfl).hom ⊗ₘ
        (liftedCochainXIso.{uR, uA, v} A L q (-(q : ℤ)) rfl).hom) ≫
        liftScalarsTensorMap.{uR, uA, v} A (K.X p) (L.X q) ≫
        (liftScalars.{uR, uA, v} A).map
          (HomologicalComplex.ιMapBifunctor K L
            (ModuleCat.moduleTensorLarge.{uA, max uR v} A)
            (ComplexShape.down ℕ) p q k h)

/-- Homology transport for the normalized comparison of total tensor complexes. -/
public abbrev LiftedTensorComparison.homologyIso
    {K L : ChainComplex (ModuleCat.{max uR uA v} A) ℕ}
    (t : LiftedTensorComparison.{uR, uA, v} A K L)
    (n : ℕ) (i : ℤ) (h : -(n : ℤ) = i) :
    (liftedCochain.{uR, uA, v} A K ⊗ liftedCochain.{uR, uA, v} A L).homology i ≅
      (liftScalars.{uR, uA, v} A).obj ((chainTensor.{uR, uA, v} K L).homology n) :=
  (HomologicalComplex.homologyFunctor _ _ i).mapIso t.iso ≪≫
    liftedCochainHomologyIso.{uR, uA, v} A (chainTensor.{uR, uA, v} K L) n i h

/-- The homology cross product of two chain complexes, characterized on classes of cycles.
This is the homological-indexing form of the construction in Tag 068H. -/
public structure ChainHomologyProduct
    (K L : ChainComplex (ModuleCat.{max uR uA v} A) ℕ) (n m : ℕ) where
  /-- The product on homology. -/
  map : ((ModuleCat.moduleTensorLarge.{uA, max uR v} A).obj (K.homology n)).obj
      (L.homology m) ⟶
    (chainTensor.{uR, uA, v} K L).homology (n + m)
  /-- Tensoring cycle representatives computes the product, exactly as in Tag 068H. -/
  maps_cycles :
    ∃ z : ((ModuleCat.moduleTensorLarge.{uA, max uR v} A).obj (K.cycles n)).obj
        (L.cycles m) ⟶
        (chainTensor.{uR, uA, v} K L).cycles (n + m),
      z ≫ (chainTensor.{uR, uA, v} K L).iCycles (n + m) =
          moduleTensorMap.{uR, uA, v} (K.iCycles n) (L.iCycles m) ≫
            HomologicalComplex.ιMapBifunctor K L
              (ModuleCat.moduleTensorLarge.{uA, max uR v} A)
              (ComplexShape.down ℕ) n m (n + m) rfl ∧
        moduleTensorMap.{uR, uA, v} (K.homologyπ n) (L.homologyπ m) ≫ map =
          z ≫ (chainTensor.{uR, uA, v} K L).homologyπ (n + m)

/-- The chain homology product agrees with Tag 068H through the canonical homology
isomorphisms for restriction of scalars and extension by zero, and the normalized comparison
of total tensor complexes. -/
public def ChainHomologyProduct.AgreesWith068H
    {K L : ChainComplex (ModuleCat.{max uR uA v} A) ℕ} {n m : ℕ}
    (c : ChainHomologyProduct.{uR, uA, v} A K L n m) : Prop :=
  let B := ULift.{max uR v} A
  let P := liftedCochain.{uR, uA, v} A K
  let Q := liftedCochain.{uR, uA, v} A L
  ∃ (hP : P.KFlat) (hQ : Q.KFlat)
    (t : LiftedTensorComparison.{uR, uA, v} A K L),
    ((liftedCochainHomologyIso.{uR, uA, v} A K n (-(n : ℤ)) rfl).hom ⊗ₘ
        (liftedCochainHomologyIso.{uR, uA, v} A L m (-(m : ℤ)) rfl).hom) ≫
        liftScalarsTensorMap.{uR, uA, v} A (K.homology n) (L.homology m) ≫
        (liftScalars.{uR, uA, v} A).map c.map =
      ((DerivedCategory.homologyFunctorFactors
          (ModuleCat B) (-(n : ℤ))).inv.app P ⊗ₘ
        (DerivedCategory.homologyFunctorFactors
          (ModuleCat B) (-(m : ℤ))).inv.app Q) ≫
        (RingTheory.TorProducts.cohomologyTensorProduct
          (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)
          (-(n : ℤ)) (-(m : ℤ))).map ≫
        (DerivedCategory.homologyFunctor
          (ModuleCat B) (-(n : ℤ) + -(m : ℤ))).map
          ((canonicalDerivedTensorProduct B).comparison P Q hP hQ).hom ≫
        (DerivedCategory.homologyFunctorFactors
          (ModuleCat B) (-(n : ℤ) + -(m : ℤ))).hom.app (P ⊗ Q) ≫
        (t.homologyIso A (n + m) (-(n : ℤ) + -(m : ℤ)) (by omega)).hom

/-- Resolution-level data inducing one component of the Tor cross product.  The chain map `μ`
lifts the identity of `M ⊗ N`; `baseChange` is the canonical monoidal comparison for extension
of scalars; and `product_eq` says that the advertised product is precisely the resulting map on
homology. -/
public structure ResolutionModel (f : R →+* A) (n m : ℕ)
    (product :
      (torBaseChange.{uR, uA, v} R A f n).prod (torBaseChange.{uR, uA, v} R A f m) ⋙
          Functor.uncurry.obj (ModuleCat.moduleTensorLarge.{uA, max uR v} A) ⟶
        Functor.uncurry.obj (ModuleCat.moduleTensorLarge.{uR, max uA v} R) ⋙
          torBaseChange.{uR, uA, v} R A f (n + m))
    (M N : ModuleCat.{max uR uA v} R)
    (P : ProjectiveResolution M) (Q : ProjectiveResolution N)
    (T : ProjectiveResolution
      (((ModuleCat.moduleTensorLarge.{uR, max uA v} R).obj M).obj N)) where
  /-- The normalized comparison from the total tensor product resolution. -/
  μ : chainTensor.{uA, uR, v} P.complex Q.complex ⟶ T.complex
  /-- In degree zero, `μ` induces the identity of `M ⊗ N`. -/
  μ_zero :
    HomologicalComplex.ιMapBifunctor P.complex Q.complex
        (ModuleCat.moduleTensorLarge.{uR, max uA v} R)
        (ComplexShape.down ℕ) 0 0 0 rfl ≫ μ.f 0 ≫ T.π.f 0 =
      moduleTensorMap.{uA, uR, v} (P.π.f 0) (Q.π.f 0)
  /-- Every other comparison lifting the identity on zeroth homology is chain homotopic to
  `μ`, as in Tags 0649 and 064A. -/
  μ_unique (ν : chainTensor.{uA, uR, v} P.complex Q.complex ⟶ T.complex)
      (hν :
        HomologicalComplex.ιMapBifunctor P.complex Q.complex
            (ModuleCat.moduleTensorLarge.{uR, max uA v} R)
            (ComplexShape.down ℕ) 0 0 0 rfl ≫ ν.f 0 ≫ T.π.f 0 =
          moduleTensorMap.{uA, uR, v} (P.π.f 0) (Q.π.f 0)) :
    Nonempty (Homotopy μ ν)
  /-- The standard base-change map between the two total complexes. -/
  baseChange :
    chainTensor.{uR, uA, v}
      (((extensionScalars.{uR, uA, v} f).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj P.complex)
        (((extensionScalars.{uR, uA, v} f).mapHomologicalComplex
          (ComplexShape.down ℕ)).obj Q.complex) ⟶
      ((extensionScalars.{uR, uA, v} f).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj
          (chainTensor.{uA, uR, v} P.complex Q.complex)
  /-- On each homogeneous summand, `baseChange` is the usual tensor base-change map. -/
  baseChange_ι (p q k : ℕ) (h : p + q = k) :
    letI := f.toAlgebra
    HomologicalComplex.ιMapBifunctor _ _
        (ModuleCat.moduleTensorLarge.{uA, max uR v} A)
        (ComplexShape.down ℕ) p q k h ≫ baseChange.f k =
      (TensorProduct.AlgebraTensorModule.distribBaseChange
        R A (P.complex.X p) (Q.complex.X q)).symm.toModuleIso.hom ≫
        (extensionScalars f).map
          (HomologicalComplex.ιMapBifunctor P.complex Q.complex
            (ModuleCat.moduleTensorLarge.{uR, max uA v} R)
            (ComplexShape.down ℕ) p q k h)
  /-- The cocycle product of Tag 068H on the two scalar-extended resolutions. -/
  cohomologyProduct : ChainHomologyProduct.{uR, uA, v} A
    (((extensionScalars.{uR, uA, v} f).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj P.complex)
    (((extensionScalars.{uR, uA, v} f).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj Q.complex) n m
  /-- The cocycle product is the canonical derived-category product of Tag 068H, transported along
  the explicit universe lift. -/
  cohomologyProduct_agreesWith068H : cohomologyProduct.AgreesWith068H
  /-- After the standard resolution identifications, the natural product is the cocycle
  product of Tag 068H followed by the homology map induced by `μ`. -/
  product_eq :
    product.app (M, N) ≫ (T.isoLeftDerivedObj (extensionScalars f) (n + m)).hom =
      moduleTensorMap.{uR, uA, v}
          (P.isoLeftDerivedObj (extensionScalars f) n).hom
          (Q.isoLeftDerivedObj (extensionScalars f) m).hom ≫
        cohomologyProduct.map ≫
        HomologicalComplex.homologyMap
          (baseChange ≫
            ((extensionScalars.{uR, uA, v} f).mapHomologicalComplex
              (ComplexShape.down ℕ)).map μ) (n + m)

/-- A functorial, normalized system of Tor cross products in all bidegrees. -/
public structure System (f : R →+* A) where
  /-- The cross product, natural in both module arguments. -/
  product (n m : ℕ) :
    (torBaseChange.{uR, uA, v} R A f n).prod (torBaseChange.{uR, uA, v} R A f m) ⋙
        Functor.uncurry.obj (ModuleCat.moduleTensorLarge.{uA, max uR v} A) ⟶
      Functor.uncurry.obj (ModuleCat.moduleTensorLarge.{uR, max uA v} R) ⋙
        torBaseChange.{uR, uA, v} R A f (n + m)
  /-- Every component is induced by the normalized comparison of arbitrary projective
  resolutions and the cocycle product of Tag 068H. -/
  resolution (n m : ℕ) (M N : ModuleCat.{max uR uA v} R)
      (P : ProjectiveResolution M) (Q : ProjectiveResolution N)
      (T : ProjectiveResolution
        (((ModuleCat.moduleTensorLarge.{uR, max uA v} R).obj M).obj N)) :
    Nonempty (ResolutionModel R A f n m (product n m) M N P Q T)
  /-- Under the canonical maps from zeroth derived functors, the bidegree `(0,0)` product is
  ordinary tensor base change.  For `M = N = R` this is the normalization `1 ⊗ 1 ↦ 1`. -/
  degree_zero (M N : ModuleCat.{max uR uA v} R) :
    (product 0 0).app (M, N) ≫
        (extensionScalars.{uR, uA, v} f).fromLeftDerivedZero.app
          (((ModuleCat.moduleTensorLarge.{uR, max uA v} R).obj M).obj N) =
      moduleTensorMap.{uR, uA, v}
          ((extensionScalars.{uR, uA, v} f).fromLeftDerivedZero.app M)
          ((extensionScalars.{uR, uA, v} f).fromLeftDerivedZero.app N) ≫
        zeroBaseChange.{uR, uA, v} R A f M N
  /-- The resolution characterization determines the natural transformation uniquely. Thus the
  product is independent of all three resolutions and of the normalized comparison map. -/
  product_unique (n m : ℕ)
      (q :
        (torBaseChange.{uR, uA, v} R A f n).prod
              (torBaseChange.{uR, uA, v} R A f m) ⋙
            Functor.uncurry.obj (ModuleCat.moduleTensorLarge.{uA, max uR v} A) ⟶
          Functor.uncurry.obj (ModuleCat.moduleTensorLarge.{uR, max uA v} R) ⋙
            torBaseChange.{uR, uA, v} R A f (n + m))
      (hq : ∀ (M N : ModuleCat.{max uR uA v} R)
        (P : ProjectiveResolution M) (Q : ProjectiveResolution N)
        (T : ProjectiveResolution
          (((ModuleCat.moduleTensorLarge.{uR, max uA v} R).obj M).obj N)),
          Nonempty (ResolutionModel R A f n m q M N P Q T)) :
    q = product n m

end TorCrossProduct

end
