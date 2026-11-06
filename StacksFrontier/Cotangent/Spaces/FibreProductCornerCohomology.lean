module

public import StacksFrontier.Cotangent.Spaces.FibreProductCornerStalkTriangle
public import StacksFrontier.Cotangent.Spaces.FibreProductStalkRings
public import StacksFrontier.Homology.Tor.ChangeOfRingsEquiv
public import StacksFrontier.RingTheory.WeaklyEtale.RingEquiv
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleLocalRingFibreProduct

/-!
# Cohomology of the object `E` of Stacks 09DK (Stacks 09DM)

Let `X ⟶ Z` and `Y ⟶ Z` be morphisms of algebraic spaces over `S`, `W = X ×_Z Y` with projections
`p` and `q`, and `E` an object fitting into the upper right corner of the diagram of Stacks 09DK.
This file proves Stacks 09DM: `H^0(E) = H^{-1}(E) = 0`, and at a geometric point `w̄` of `W`,
`H^{-2}(E)_{w̄} ≅ Tor_1^R(A, B) ⊗_{A ⊗_R B} C` as `C`-modules, for the étale local rings
`R = 𝒪_{Z, f(p(w̄))}`, `A = 𝒪_{X, p(w̄)}`, `B = 𝒪_{Y, q(w̄)}`, `C = 𝒪_{W, w̄}`.

The proof is the source's. The stalk at `w̄` of the right column `Lq^*L_{Y/Z} ⟶ L_{W/X} ⟶ E ⟶` of
the diagram is a distinguished triangle on `L_{B/R} ⊗^𝐋_B C ⟶ L_{C/R} ⟶ L_{C/A}` for the stalk
rings (`CategoryTheory.Sheaf.exists_distTriang_derivedModuleFiber_fundamental`); these are the
étale local rings (`StacksFrontier.Cotangent.Spaces.FibreProductStalkRings`); `C` is weakly étale over
`A ⊗_R B` (`AlgebraicGeometry.Space.cartesian_etaleStalk_tensor_weaklyEtale`), so the stalk of `E`
is the base change to `C` of the object `E` of the nine diagram of `R → A, R → B`, whose
cohomology is Stacks 09DB. The cohomology sheaves are read off on stalks at the geometric points
(`AlgebraicGeometry.Space.isZero_homology_of_forall_derivedStalk`).

## Main results

* `AlgebraicGeometry.Space.fiberProduct_upperRightCorner_homology`: **Stacks 09DM**.
* `AlgebraicGeometry.Space.upperRightCorner_homology`: the same for any cartesian square.
* `AlgebraicGeometry.Space.upperRightCorner_derivedStalk`: the statement at one geometric point.
* `CommAlgCat.homology_cone_fundamentalMor_of_ringEquiv`: the ring-theoretic content, transported
  along isomorphisms of rings.

## Implementation notes

The stalk `H^{-2}(E)_{w̄}` is a module over the stalk at `w̄` of the structure sheaf, which is
identified with `C` by `AlgebraicGeometry.Space.smallEtaleStructureSheafULiftStalkEquiv`; the
isomorphism is stated after extension of scalars along that identification. The map
`χ : A ⊗_R B → C` is pinned down by its restrictions to `A` and `B`, the canonical maps of étale
local rings, and `Tor_1^R(A, B)` carries its canonical `A ⊗_R B`-module structure
(`CommAlgCat.torOneTensorProductModule`).

## References

* [Stacks Project, Tag 09DM](https://stacks.math.columbia.edu/tag/09DM)
* [Stacks Project, Tag 09DK](https://stacks.math.columbia.edu/tag/09DK)
* [Stacks Project, Tag 09DB](https://stacks.math.columbia.edu/tag/09DB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open scoped TensorProduct

universe u

namespace CommAlgCat

section Transport

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe v

variable {R' A' B' C' : Type v} [CommRing R'] [CommRing A'] [CommRing B'] [CommRing C']
  [Algebra R' A'] [Algebra R' B'] [Algebra R' C'] [Algebra A' C'] [Algebra B' C']
  [IsScalarTower R' A' C'] [IsScalarTower R' B' C']
  {R A B C : Type v} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra R A] [Algebra R B]

/-- **The ring-theoretic content of Stacks 09DM, transported along isomorphisms of rings.** Let
`R' → A', B' → C'` be a commutative diagram of rings isomorphic, by `ρ`, to `R → A, B → C`, where
`C` is weakly étale over `A ⊗_R B` along `φ`. Then every cone `E_C` of
`L_{B'/R'} ⊗^𝐋_{B'} C' ⟶ L_{C'/R'} ⟶ L_{C'/A'}` has `H^i(E_C) = 0` for `i ≥ -1`, and
`H^{-2}(E_C) ⊗_{C'} C ≅ Tor_1^R(A, B) ⊗_{A ⊗_R B} C` as `C`-modules. -/
theorem homology_cone_fundamentalMor_of_ringEquiv (φ : A ⊗[R] B →+* C)
    (hW : @Algebra.WeaklyEtale _ _ _ _ φ.toAlgebra)
    (ρR : R' ≃+* R) (ρA : A' ≃+* A) (ρB : B' ≃+* B) (ρC : C' ≃+* C)
    (hA : ∀ r, ρA (algebraMap R' A' r) = algebraMap R A (ρR r))
    (hB : ∀ r, ρB (algebraMap R' B' r) = algebraMap R B (ρR r))
    (hAC : ∀ a, ρC (algebraMap A' C' a) = φ (ρA a ⊗ₜ[R] 1))
    (hBC : ∀ b, ρC (algebraMap B' C' b) = φ (1 ⊗ₜ[R] ρB b))
    {EC : DerivedCategory (ModuleCat.{v} C')}
    {b' : cotangentComplexDerived.{v, v} A' (CommAlgCat.of A' C') ⟶ EC}
    {e' : EC ⟶ (fundamentalVertex₁.{v, v, v + 1, v + 1} R' B' C')⟦(1 : ℤ)⟧}
    (hC : Triangle.mk (fundamentalMor₁.{v} R' B' C' ≫ fundamentalMor₂.{v} R' A' C') b' e' ∈
      distTriang (DerivedCategory (ModuleCat.{v} C'))) :
    (∀ i : ℤ, -1 ≤ i → IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} C') i).obj EC)) ∧
      Nonempty ((ModuleCat.extendScalars.{v, v, v} ρC.toRingHom).obj
          ((DerivedCategory.homologyFunctor (ModuleCat.{v} C') (-2)).obj EC) ≅
        (ModuleCat.extendScalars.{v, v, v} φ).obj (torOneTensorProductModule R A B)) := by
  let : Algebra (A' ⊗[R'] B') C' :=
    (Algebra.TensorProduct.lift (IsScalarTower.toAlgHom R' A' C') (IsScalarTower.toAlgHom R' B' C')
      fun _ _ => Commute.all _ _).toRingHom.toAlgebra
  have : IsScalarTower R' (A' ⊗[R'] B') C' := IsScalarTower.of_algebraMap_eq fun r =>
    ((Algebra.TensorProduct.lift (IsScalarTower.toAlgHom R' A' C')
      (IsScalarTower.toAlgHom R' B' C') fun _ _ => Commute.all _ _).commutes r).symm
  have : IsScalarTower A' (A' ⊗[R'] B') C' := IsScalarTower.of_algebraMap_eq fun a => by
    show _ = (Algebra.TensorProduct.lift _ _ _) (a ⊗ₜ[R'] (1 : B'))
    simp
  have : IsScalarTower B' (A' ⊗[R'] B') C' := IsScalarTower.of_algebraMap_eq fun b => by
    show _ = (Algebra.TensorProduct.lift _ _ _) ((1 : A') ⊗ₜ[R'] b)
    simp
  have hτ : ∀ t, ρC (algebraMap (A' ⊗[R'] B') C' t) =
      φ (TorChangeOfRings.equivTensorProductRingEquiv ρR ρA ρB hA hB t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      show ρC ((Algebra.TensorProduct.lift _ _ _) (a ⊗ₜ[R'] b)) =
        φ (TorChangeOfRings.equivTensorProductMap ρR ρA ρB hA hB (a ⊗ₜ[R'] b))
      rw [TorChangeOfRings.equivTensorProductMap_tmul, Algebra.TensorProduct.lift_tmul, map_mul]
      show ρC (algebraMap A' C' a) * ρC (algebraMap B' C' b) = _
      rw [hAC, hBC, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  have : Algebra.WeaklyEtale (A' ⊗[R'] B') C' :=
    @Algebra.WeaklyEtale.of_ringEquiv _ _ _ _ _ _ _ _ φ.toAlgebra _ hW
      (TorChangeOfRings.equivTensorProductRingEquiv ρR ρA ρB hA hB) ρC hτ
  obtain ⟨hz, ⟨e⟩⟩ := homology_cone_fundamentalMor_of_weaklyEtale R' A' B' C' hC
  have hcomp : ρC.toRingHom.comp (algebraMap (A' ⊗[R'] B') C') =
      φ.comp (TorChangeOfRings.equivTensorProductRingEquiv ρR ρA ρB hA hB).toRingHom :=
    RingHom.ext hτ
  exact ⟨hz, ⟨(ModuleCat.extendScalars.{v, v, v} ρC.toRingHom).mapIso e ≪≫
    ((ModuleCat.extendScalarsComp (algebraMap (A' ⊗[R'] B') C') ρC.toRingHom).app _).symm ≪≫
    eqToIso (congrArg (fun k => (ModuleCat.extendScalars.{v, v, v} k).obj
      (torOneTensorProductModule R' A' B')) hcomp) ≪≫
    (ModuleCat.extendScalarsComp
      (TorChangeOfRings.equivTensorProductRingEquiv ρR ρA ρB hA hB).toRingHom φ).app _ ≪≫
    (ModuleCat.extendScalars.{v, v, v} φ).mapIso
      (TorChangeOfRings.extendScalarsTorIsoOfRingEquiv ρR ρA ρB hA hB 1)⟩⟩

end Transport

end CommAlgCat

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y Z W : AlgebraicSpaces B S hS} {f : X ⟶ Z} {g : Y ⟶ Z} {p : W ⟶ X} {q : W ⟶ Y}

attribute [local instance] HasDerivedCategory.standard

attribute [-instance] CategoryTheory.Sheaf.hasSheafifyAddCommGrpCat
  CategoryTheory.Sheaf.wEqualsLocallyBijectiveAddCommGrpCat

attribute [local instance high] hasSheafify_smallEtaleRingedToposULift
  wEqualsLocallyBijective_smallEtaleRingedToposULift

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out without
this shortcut). -/
local instance (priority := high) hasPullback_presheaf_fibreProductCornerCohomology
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- **Stacks 09DM at a geometric point.** -/
theorem upperRightCorner_derivedStalk (hpb : IsPullback p q f g)
    (E : Triangulated.UpperRightCorner (transitivityUnit p f) (transitivityCounit p f)
      (fibreProductColumnUnit hpb.w) (fibreProductColumnCounit hpb.w))
    (w : GeometricPoint B S hS W.1) :
    (∀ i : ℤ, -1 ≤ i → IsZero ((DerivedCategory.homologyFunctor _ i).obj
      ((derivedStalk B S hS W w).obj E.obj))) ∧
    letI : Algebra (etaleLocalRing B S hS Z.1 (geometricPointMap f.hom (geometricPointMap p.hom w)))
        (etaleLocalRing B S hS X.1 (geometricPointMap p.hom w)) :=
      (etaleLocalRingMap X.2 f.hom (geometricPointMap p.hom w)).toAlgebra
    letI : Algebra (etaleLocalRing B S hS Z.1 (geometricPointMap f.hom (geometricPointMap p.hom w)))
        (etaleLocalRing B S hS Y.1 (geometricPointMap q.hom w)) :=
      ((eqToHom (congrArg (etaleLocalRing B S hS Z.1)
          (congrArg (fun k : W ⟶ Z => geometricPointMap k.hom w) hpb.w)) ≫
        CommRingCat.ofHom (etaleLocalRingMap Y.2 g.hom (geometricPointMap q.hom w))).hom).toAlgebra
    ∃ χ : etaleLocalRing B S hS X.1 (geometricPointMap p.hom w) ⊗[etaleLocalRing B S hS Z.1
        (geometricPointMap f.hom (geometricPointMap p.hom w))]
        etaleLocalRing B S hS Y.1 (geometricPointMap q.hom w) →+* etaleLocalRing B S hS W.1 w,
      χ.comp Algebra.TensorProduct.includeLeftRingHom = etaleLocalRingMap W.2 p.hom w ∧
      χ.comp Algebra.TensorProduct.includeRight.toRingHom = etaleLocalRingMap W.2 q.hom w ∧
      Nonempty ((ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
          (smallEtaleStructureSheafULiftStalkEquiv B S hS W w).toRingHom).obj
          ((Stacks.sheafModuleFiberOfCommRing (geometricSitePoint B S hS W w)
            (smallEtaleStructureSheafULift B S hS W)).obj
            ((DerivedCategory.homologyFunctor (smallEtaleModulesULift B S hS W) (-2)).obj E.obj)) ≅
        (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} χ).obj
          (CommAlgCat.torOneTensorProductModule _ _ _)) := by
  have hT := E.right_distinguished
  rw [fibreProductColumnUnit_comp_transitivityCounit_eq hpb.w] at hT
  obtain ⟨b', e', hC⟩ := Sheaf.exists_distTriang_derivedModuleFiber_fundamental
    (SmallEtale.topology B S hS W.1) (geometricSitePoint B S hS W w)
    (RingedToposHom.towerBaseMap.{u, u + 1, u, u, u + 1, u, u, u + 1, u + 1}
      (smallEtaleRingedToposHomULift g) (smallEtaleRingedToposHomULift q))
          (smallEtaleRingedToposHomULift q).fSharpInverseImage (columnBaseMap hpb.w)
    (sq_columnBaseMap hpb.w) (columnChain hpb.w)
    (isPointStalkBaseMap_columnChain hpb.w _) (derivedPullbackCotangentComplexIso q g) hT
  let : Algebra (((geometricSitePoint B S hS W w).presheafFiber (A := CommRingCat.{u + 1})).obj
      ((inverseImageCommRingFunctor.{u + 1, u + 1, u, u + 1, u, u + 1}
        (smallToposMorphism B S hS q)).obj
        ((inverseImageCommRingFunctor.{u + 1, u + 1, u, u + 1, u, u + 1}
          (smallToposMorphism B S hS g)).obj (smallEtaleStructureSheafULift B S hS Z))).obj)
              (((geometricSitePoint B S hS W w).presheafFiber (A := CommRingCat.{u + 1})).obj
                  ((inverseImageCommRingFunctor.{u + 1, u + 1, u, u + 1, u, u + 1}
        (smallToposMorphism B S hS q)).obj (smallEtaleStructureSheafULift B S hS Y)).obj) :=
            (((geometricSitePoint B S hS W w).presheafFiber (A := CommRingCat.{u + 1})).map
                (RingedToposHom.towerBaseMap.{u, u + 1, u, u, u + 1, u, u, u + 1, u + 1}
      (smallEtaleRingedToposHomULift g) (smallEtaleRingedToposHomULift q)).hom).hom.toAlgebra
  let : Algebra (((geometricSitePoint B S hS W w).presheafFiber (A := CommRingCat.{u + 1})).obj
      ((inverseImageCommRingFunctor.{u + 1, u + 1, u, u + 1, u, u + 1}
        (smallToposMorphism B S hS q)).obj (smallEtaleStructureSheafULift B S hS Y)).obj)
            (((geometricSitePoint B S hS W w).presheafFiber (A := CommRingCat.{u + 1})).obj
                (smallEtaleStructureSheafULift B S hS W).obj) := (((geometricSitePoint B S hS W
                    w).presheafFiber (A := CommRingCat.{u + 1})).map (smallEtaleRingedToposHomULift
                        q).fSharpInverseImage.hom).hom.toAlgebra
  let : Algebra (((geometricSitePoint B S hS W w).presheafFiber (A := CommRingCat.{u + 1})).obj
      ((inverseImageCommRingFunctor.{u + 1, u + 1, u, u + 1, u, u + 1}
        (smallToposMorphism B S hS q)).obj
        ((inverseImageCommRingFunctor.{u + 1, u + 1, u, u + 1, u, u + 1}
          (smallToposMorphism B S hS g)).obj (smallEtaleStructureSheafULift B S hS Z))).obj)
              (((geometricSitePoint B S hS W w).presheafFiber (A := CommRingCat.{u + 1})).obj
                  (smallEtaleStructureSheafULift B S hS W).obj) := (((geometricSitePoint B S hS W
                      w).presheafFiber (A := CommRingCat.{u + 1})).map
                          ((RingedToposHom.towerBaseMap.{u, u + 1, u, u, u + 1, u, u, u + 1, u + 1}
      (smallEtaleRingedToposHomULift g) (smallEtaleRingedToposHomULift q)) ≫
          (smallEtaleRingedToposHomULift q).fSharpInverseImage).hom).hom.toAlgebra
  have : IsScalarTower (((geometricSitePoint B S hS W w).presheafFiber (A := CommRingCat.{u +
      1})).obj ((inverseImageCommRingFunctor.{u + 1, u + 1, u, u + 1, u, u + 1}
        (smallToposMorphism B S hS q)).obj
        ((inverseImageCommRingFunctor.{u + 1, u + 1, u, u + 1, u, u + 1}
          (smallToposMorphism B S hS g)).obj (smallEtaleStructureSheafULift B S hS Z))).obj)
              (((geometricSitePoint B S hS W w).presheafFiber (A := CommRingCat.{u + 1})).obj
                  ((inverseImageCommRingFunctor.{u + 1, u + 1, u, u + 1, u, u + 1}
        (smallToposMorphism B S hS q)).obj (smallEtaleStructureSheafULift B S hS Y)).obj)
            (((geometricSitePoint B S hS W w).presheafFiber (A := CommRingCat.{u + 1})).obj
                (smallEtaleStructureSheafULift B S hS W).obj) :=
    Sheaf.isScalarTower_pointStalk.{u + 1, u, u} (SmallEtale.topology B S hS W.1)
      (geometricSitePoint B S hS W w) (RingedToposHom.towerBaseMap.{u, u + 1, u, u, u + 1, u, u, u
          + 1, u + 1}
      (smallEtaleRingedToposHomULift g) (smallEtaleRingedToposHomULift q))
          (smallEtaleRingedToposHomULift q).fSharpInverseImage
  let : Algebra (((geometricSitePoint B S hS W w).presheafFiber (A := CommRingCat.{u + 1})).obj
      ((inverseImageCommRingFunctor.{u + 1, u + 1, u, u + 1, u, u + 1}
        (smallToposMorphism B S hS q)).obj
        ((inverseImageCommRingFunctor.{u + 1, u + 1, u, u + 1, u, u + 1}
          (smallToposMorphism B S hS g)).obj (smallEtaleStructureSheafULift B S hS Z))).obj)
              (((geometricSitePoint B S hS W w).presheafFiber (A := CommRingCat.{u + 1})).obj
                  (liftedBaseRing (B := B) (S := S) (hS := hS) p).obj) := (((geometricSitePoint B S
                      hS W w).presheafFiber (A := CommRingCat.{u + 1})).map (columnBaseMap
                          hpb.w).hom).hom.toAlgebra
  let : Algebra (((geometricSitePoint B S hS W w).presheafFiber (A := CommRingCat.{u + 1})).obj
      (liftedBaseRing (B := B) (S := S) (hS := hS) p).obj) (((geometricSitePoint B S hS W
          w).presheafFiber (A := CommRingCat.{u + 1})).obj (smallEtaleStructureSheafULift B S hS
              W).obj) := (((geometricSitePoint B S hS W w).presheafFiber (A := CommRingCat.{u +
                  1})).map (liftedStructureMap p).hom).hom.toAlgebra
  have : IsScalarTower (((geometricSitePoint B S hS W w).presheafFiber (A := CommRingCat.{u +
      1})).obj ((inverseImageCommRingFunctor.{u + 1, u + 1, u, u + 1, u, u + 1}
        (smallToposMorphism B S hS q)).obj
        ((inverseImageCommRingFunctor.{u + 1, u + 1, u, u + 1, u, u + 1}
          (smallToposMorphism B S hS g)).obj (smallEtaleStructureSheafULift B S hS Z))).obj)
              (((geometricSitePoint B S hS W w).presheafFiber (A := CommRingCat.{u + 1})).obj
                  (liftedBaseRing (B := B) (S := S) (hS := hS) p).obj) (((geometricSitePoint B S hS
                      W w).presheafFiber (A := CommRingCat.{u + 1})).obj
                          (smallEtaleStructureSheafULift B S hS W).obj) :=
    Sheaf.isScalarTower_pointStalk_base.{u + 1, u, u} (SmallEtale.topology B S hS W.1)
      (geometricSitePoint B S hS W w) (RingedToposHom.towerBaseMap.{u, u + 1, u, u, u + 1, u, u, u
          + 1, u + 1}
      (smallEtaleRingedToposHomULift g) (smallEtaleRingedToposHomULift q))
          (smallEtaleRingedToposHomULift q).fSharpInverseImage (columnBaseMap hpb.w)
              (sq_columnBaseMap hpb.w)
  obtain ⟨φ, hφA, hφB, hW⟩ := cartesian_etaleStalk_tensor_weaklyEtale B S hS p q f g hpb w
  let : Algebra (etaleLocalRing B S hS Z.1 (geometricPointMap f.hom (geometricPointMap p.hom w)))
      (etaleLocalRing B S hS X.1 (geometricPointMap p.hom w)) :=
    (etaleLocalRingMap X.2 f.hom (geometricPointMap p.hom w)).toAlgebra
  let : Algebra (etaleLocalRing B S hS Z.1 (geometricPointMap f.hom (geometricPointMap p.hom w)))
      (etaleLocalRing B S hS Y.1 (geometricPointMap q.hom w)) :=
    ((eqToHom (congrArg (etaleLocalRing B S hS Z.1)
        (congrArg (fun k : W ⟶ Z => geometricPointMap k.hom w) hpb.w)) ≫
      CommRingCat.ofHom (etaleLocalRingMap Y.2 g.hom (geometricPointMap q.hom w))).hom).toAlgebra
  obtain ⟨hz, ⟨e⟩⟩ := CommAlgCat.homology_cone_fundamentalMor_of_ringEquiv φ hW
    (towerBaseStalkEquiv B S hS hpb.w w) (liftedBaseRingStalkEquiv B S hS p w)
    (inverseImageStalkEquiv B S hS q w) (smallEtaleStructureSheafULiftStalkEquiv B S hS W w)
    (columnBaseMap_stalk_apply hpb.w w) (towerBaseMap_stalk_apply hpb.w w)
    (fun a => (liftedStructureMap_stalk_apply p w a).trans
      (RingHom.congr_fun hφA (liftedBaseRingStalkEquiv B S hS p w a)).symm)
    (fun b => (fSharpInverseImageULift_stalk_apply w b).trans
      (RingHom.congr_fun hφB (inverseImageStalkEquiv B S hS q w b)).symm) hC
  exact ⟨hz, φ, hφA, hφB, ⟨(ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
    (smallEtaleStructureSheafULiftStalkEquiv B S hS W w).toRingHom).mapIso
      (homologyDerivedStalkIso B S hS W w E.obj (-2)) ≪≫ e⟩⟩

/-- **Stacks 09DM, for a cartesian square.** Let `p : W ⟶ X`, `q : W ⟶ Y`, `f : X ⟶ Z`,
`g : Y ⟶ Z` be a cartesian square of algebraic spaces over `S` and let `E` be an object fitting
into the upper right corner of the diagram of Stacks 09DK. Then `H^0(E) = H^{-1}(E) = 0`, and at
every geometric point `w̄` of `W`, with `R = 𝒪_{Z, f(p(w̄))}`, `A = 𝒪_{X, p(w̄)}`,
`B = 𝒪_{Y, q(w̄)}` and `C = 𝒪_{W, w̄}` the étale local rings and the canonical maps between them,
`H^{-2}(E)_{w̄} ≅ Tor_1^R(A, B) ⊗_{A ⊗_R B} C` as `C`-modules, `χ : A ⊗_R B → C` being the map
induced by the canonical maps `A → C` and `B → C`. The stalk `H^{-2}(E)_{w̄}` is a module over the
stalk of the structure sheaf, which is identified with `C` by
`AlgebraicGeometry.Space.smallEtaleStructureSheafULiftStalkEquiv`. -/
@[stacks 09DM "for every cartesian square of algebraic spaces, in particular for the fibre \
  product with its two projections (`fiberProduct_upperRightCorner_homology`), and every object \
  E fitting into the upper right corner of the diagram of 09DK"]
theorem upperRightCorner_homology (hpb : IsPullback p q f g)
    (E : Triangulated.UpperRightCorner (transitivityUnit p f) (transitivityCounit p f)
      (fibreProductColumnUnit hpb.w) (fibreProductColumnCounit hpb.w)) :
    IsZero ((DerivedCategory.homologyFunctor (smallEtaleModulesULift B S hS W) 0).obj E.obj) ∧
    IsZero ((DerivedCategory.homologyFunctor (smallEtaleModulesULift B S hS W) (-1)).obj E.obj) ∧
    ∀ w : GeometricPoint B S hS W.1,
    letI : Algebra (etaleLocalRing B S hS Z.1 (geometricPointMap f.hom (geometricPointMap p.hom w)))
        (etaleLocalRing B S hS X.1 (geometricPointMap p.hom w)) :=
      (etaleLocalRingMap X.2 f.hom (geometricPointMap p.hom w)).toAlgebra
    letI : Algebra (etaleLocalRing B S hS Z.1 (geometricPointMap f.hom (geometricPointMap p.hom w)))
        (etaleLocalRing B S hS Y.1 (geometricPointMap q.hom w)) :=
      ((eqToHom (congrArg (etaleLocalRing B S hS Z.1)
          (congrArg (fun k : W ⟶ Z => geometricPointMap k.hom w) hpb.w)) ≫
        CommRingCat.ofHom (etaleLocalRingMap Y.2 g.hom (geometricPointMap q.hom w))).hom).toAlgebra
    ∃ χ : etaleLocalRing B S hS X.1 (geometricPointMap p.hom w) ⊗[etaleLocalRing B S hS Z.1
        (geometricPointMap f.hom (geometricPointMap p.hom w))]
        etaleLocalRing B S hS Y.1 (geometricPointMap q.hom w) →+* etaleLocalRing B S hS W.1 w,
      χ.comp Algebra.TensorProduct.includeLeftRingHom = etaleLocalRingMap W.2 p.hom w ∧
      χ.comp Algebra.TensorProduct.includeRight.toRingHom = etaleLocalRingMap W.2 q.hom w ∧
      Nonempty ((ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
          (smallEtaleStructureSheafULiftStalkEquiv B S hS W w).toRingHom).obj
          ((Stacks.sheafModuleFiberOfCommRing (geometricSitePoint B S hS W w)
            (smallEtaleStructureSheafULift B S hS W)).obj
            ((DerivedCategory.homologyFunctor (smallEtaleModulesULift B S hS W) (-2)).obj E.obj)) ≅
        (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} χ).obj
          (CommAlgCat.torOneTensorProductModule _ _ _)) :=
  ⟨isZero_homology_of_forall_derivedStalk B S hS W E.obj 0 fun w =>
      (upperRightCorner_derivedStalk hpb E w).1 0 (by norm_num),
    isZero_homology_of_forall_derivedStalk B S hS W E.obj (-1) fun w =>
      (upperRightCorner_derivedStalk hpb E w).1 (-1) le_rfl,
    fun w => (upperRightCorner_derivedStalk hpb E w).2⟩

/-- **Stacks 09DM.** Let `X ⟶ Z` and `Y ⟶ Z` be morphisms of algebraic spaces over `S`, let
`W = X ×_Z Y` with projections `p` and `q`, and let `E` be the object of Stacks 09DK, i.e. any
object fitting into the upper right corner of its diagram. Then `H^0(E) = H^{-1}(E) = 0`, and
for a geometric point `w̄` of `W`,
`H^{-2}(E)_{w̄} ≅ Tor_1^R(A, B) ⊗_{A ⊗_R B} C` as `C`-modules, where `R = 𝒪_{Z, f(p(w̄))}`,
`A = 𝒪_{X, p(w̄)}`, `B = 𝒪_{Y, q(w̄)}` and `C = 𝒪_{W, w̄}` are the étale local rings,
`Tor_1^R(A, B)` carries its canonical `A ⊗_R B`-module structure, and `χ : A ⊗_R B → C` is the map
induced by the canonical maps of étale local rings. -/
@[stacks 09DM "for the fibre product X ×_Z Y with its two projections and every object E fitting \
  into the upper right corner of the diagram of 09DK: H^0(E) = H^{-1}(E) = 0, and \
  H^{-2}(E)_w ≅ Tor_1^R(A, B) ⊗_{A ⊗_R B} C as C-modules for the etale local rings R, A, B, C"]
theorem fiberProduct_upperRightCorner_homology (f : X ⟶ Z) (g : Y ⟶ Z) :
    ∀ E : Triangulated.UpperRightCorner (transitivityUnit (ObjectProperty.homMk (pullback.fst f.hom
        g.hom) : (AlgebraicSpaces.fiberProduct B S hS f g) ⟶ X) f) (transitivityCounit
            (ObjectProperty.homMk (pullback.fst f.hom g.hom) : (AlgebraicSpaces.fiberProduct B S hS
                f g) ⟶ X) f)
      (fibreProductColumnUnit (AlgebraicSpaces.isPullback_fiberProduct B S hS f g).w)
      (fibreProductColumnCounit (AlgebraicSpaces.isPullback_fiberProduct B S hS f g).w),
      IsZero ((DerivedCategory.homologyFunctor (smallEtaleModulesULift B S hS
          (AlgebraicSpaces.fiberProduct B S hS f g)) 0).obj E.obj) ∧
      IsZero ((DerivedCategory.homologyFunctor (smallEtaleModulesULift B S hS
          (AlgebraicSpaces.fiberProduct B S hS f g)) (-1)).obj E.obj) ∧
      ∀ w : GeometricPoint B S hS (AlgebraicSpaces.fiberProduct B S hS f g).1,
      letI : Algebra (etaleLocalRing B S hS Z.1 (geometricPointMap f.hom (geometricPointMap
          (ObjectProperty.homMk (pullback.fst f.hom g.hom) : (AlgebraicSpaces.fiberProduct B S hS f
              g) ⟶ X).hom w)))
          (etaleLocalRing B S hS X.1 (geometricPointMap (ObjectProperty.homMk (pullback.fst f.hom
              g.hom) : (AlgebraicSpaces.fiberProduct B S hS f g) ⟶ X).hom w)) :=
        (etaleLocalRingMap X.2 f.hom (geometricPointMap (ObjectProperty.homMk (pullback.fst f.hom
            g.hom) : (AlgebraicSpaces.fiberProduct B S hS f g) ⟶ X).hom w)).toAlgebra
      letI : Algebra (etaleLocalRing B S hS Z.1 (geometricPointMap f.hom (geometricPointMap
          (ObjectProperty.homMk (pullback.fst f.hom g.hom) : (AlgebraicSpaces.fiberProduct B S hS f
              g) ⟶ X).hom w)))
          (etaleLocalRing B S hS Y.1 (geometricPointMap (ObjectProperty.homMk (pullback.snd f.hom
              g.hom) : (AlgebraicSpaces.fiberProduct B S hS f g) ⟶ Y).hom w)) :=
        ((eqToHom (congrArg (etaleLocalRing B S hS Z.1)
            (congrArg (fun k : (AlgebraicSpaces.fiberProduct B S hS f g) ⟶ Z => geometricPointMap
                k.hom w) (AlgebraicSpaces.isPullback_fiberProduct B S hS f g).w)) ≫
          CommRingCat.ofHom (etaleLocalRingMap Y.2 g.hom (geometricPointMap (ObjectProperty.homMk
              (pullback.snd f.hom g.hom) : (AlgebraicSpaces.fiberProduct B S hS f g) ⟶ Y).hom
                  w))).hom).toAlgebra
      ∃ χ : etaleLocalRing B S hS X.1 (geometricPointMap (ObjectProperty.homMk (pullback.fst f.hom
          g.hom) : (AlgebraicSpaces.fiberProduct B S hS f g) ⟶ X).hom w) ⊗[etaleLocalRing B S hS Z.1
          (geometricPointMap f.hom (geometricPointMap (ObjectProperty.homMk (pullback.fst f.hom
              g.hom) : (AlgebraicSpaces.fiberProduct B S hS f g) ⟶ X).hom w))]
          etaleLocalRing B S hS Y.1 (geometricPointMap (ObjectProperty.homMk (pullback.snd f.hom
              g.hom) : (AlgebraicSpaces.fiberProduct B S hS f g) ⟶ Y).hom w) →+* etaleLocalRing B S
                  hS (AlgebraicSpaces.fiberProduct B S hS f g).1 w,
        χ.comp Algebra.TensorProduct.includeLeftRingHom = etaleLocalRingMap
            (AlgebraicSpaces.fiberProduct B S hS f g).2 (ObjectProperty.homMk (pullback.fst f.hom
                g.hom) : (AlgebraicSpaces.fiberProduct B S hS f g) ⟶ X).hom w ∧
        χ.comp Algebra.TensorProduct.includeRight.toRingHom = etaleLocalRingMap
            (AlgebraicSpaces.fiberProduct B S hS f g).2 (ObjectProperty.homMk (pullback.snd f.hom
                g.hom) : (AlgebraicSpaces.fiberProduct B S hS f g) ⟶ Y).hom w ∧
        Nonempty ((ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
            (smallEtaleStructureSheafULiftStalkEquiv B S hS (AlgebraicSpaces.fiberProduct B S hS f
                g) w).toRingHom).obj
            ((Stacks.sheafModuleFiberOfCommRing (geometricSitePoint B S hS
                (AlgebraicSpaces.fiberProduct B S hS f g) w)
              (smallEtaleStructureSheafULift B S hS (AlgebraicSpaces.fiberProduct B S hS f g))).obj
              ((DerivedCategory.homologyFunctor (smallEtaleModulesULift B S hS
                  (AlgebraicSpaces.fiberProduct B S hS f g)) (-2)).obj E.obj)) ≅
          (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} χ).obj
            (CommAlgCat.torOneTensorProductModule _ _ _)) :=
  fun E => upperRightCorner_homology (AlgebraicSpaces.isPullback_fiberProduct B S hS f g) E

end AlgebraicGeometry.Space

end
