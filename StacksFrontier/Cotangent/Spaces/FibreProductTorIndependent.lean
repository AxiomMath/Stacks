module

public import StacksFrontier.Cotangent.Spaces.FibreProductCornerCohomology
public import StacksFrontier.Cotangent.TensorProductTorIndependent
public import StacksFrontier.Homology.DerivedCategory.IsZero
public import StacksFrontier.Homology.Tor.IndependenceUniverseChange

/-!
# Fibre products of Tor independent algebraic spaces and the cotangent complex (Stacks 09DL)

Let `X ⟶ Z` and `Y ⟶ Z` be morphisms of algebraic spaces over `S`, `W = X ×_Z Y` with projections
`p` and `q`. If `X` and `Y` are Tor independent over `Z`, then the object `E` in the upper right
corner of the diagram of Stacks 09DK is zero, and the canonical map
`Lp^*L_{X/Z} ⊕ Lq^*L_{Y/Z} ⟶ L_{W/Z}` is an isomorphism.

The proof checks the vanishing of `E` on derived stalks at the geometric points `w̄` of `W`
(`AlgebraicGeometry.Space.isZero_homology_of_forall_derivedStalk`). As in the proof of Stacks 09DM,
the derived stalk of `E` at `w̄` is a cone of `L_{B/R} ⊗^𝐋_B C ⟶ L_{C/R} ⟶ L_{C/A}` for the étale
local rings `R`, `A`, `B`, `C` at `w̄`, where `C` is weakly étale over `A ⊗_R B`; its cohomology is
that of the object `E` of the nine diagram of `R → A, R → B` tensored up to `C`, and that object
vanishes for Tor independent `A` and `B` by Stacks 09DA.

## Main results

* `AlgebraicGeometry.Space.fiberProduct_cotangentComplex_of_torIndependent`: **Stacks 09DL**.
* `AlgebraicGeometry.Space.isZero_upperRightCorner_of_torIndependent`,
  `AlgebraicGeometry.Space.isIso_fibreProductBiprodMap_of_torIndependent`: the two assertions for
  any cartesian square.
* `CommAlgCat.isZero_cone_fundamentalMor_of_torIndependent`: the ring-theoretic content.

## References

* [Stacks Project, Tag 09DL](https://stacks.math.columbia.edu/tag/09DL)
* [Stacks Project, Tag 09DK](https://stacks.math.columbia.edu/tag/09DK)
* [Stacks Project, Tag 09DA](https://stacks.math.columbia.edu/tag/09DA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open scoped TensorProduct

universe u

namespace CommAlgCat

section NineDiagram

attribute [local instance] Algebra.TensorProduct.rightAlgebra
attribute [local instance] HasDerivedCategory.standard

variable (R : Type u) [CommRing R] (A B : Type u) [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]

/-- The first map of the middle row of the nine diagram, the first morphism of the fundamental
triangle of `R → A → A ⊗_R B`, is the canonical map `L_{A/R} ⊗^𝐋_A (A ⊗_R B) ⟶ L_{A ⊗_R B/R}`. -/
theorem fundamentalMor₁_eq_cotangentTensorProductLeftMap :
    fundamentalMor₁ R A (A ⊗[R] B) = cotangentTensorProductLeftMap R A B :=
  rfl

/-- The first map of the middle column of the nine diagram, the first morphism of the fundamental
triangle of `R → B → A ⊗_R B`, is the canonical map `L_{B/R} ⊗^𝐋_B (A ⊗_R B) ⟶ L_{A ⊗_R B/R}`. -/
theorem fundamentalMor₁_eq_cotangentTensorProductRightMap :
    fundamentalMor₁ R B (A ⊗[R] B) = cotangentTensorProductRightMap R A B :=
  rfl

/-- If `A` and `B` are Tor independent over `R`, the object `E` of the nine diagram of
Tag 09D9 vanishes. -/
theorem isZero_canonicalTensorProductNineDiagram_upperRight_of_torIndependent
    (hTor : RingTheory.TorIndependence.TorIndependent R A B) :
    IsZero (canonicalTensorProductNineDiagram R A B).upperRight :=
  TensorProductNineDiagram.isZero_upperRight_of_torIndependent R A B _ hTor
    ((canonicalTensorProductNineDiagram_spec R A B).1.trans
      (fundamentalMor₁_eq_cotangentTensorProductLeftMap R A B))
    ((canonicalTensorProductNineDiagram_spec R A B).2.2.2.1.trans
      (fundamentalMor₁_eq_cotangentTensorProductRightMap R A B))

variable (C : Type u) [CommRing C] [Algebra (A ⊗[R] B) C] [Algebra R C] [Algebra A C] [Algebra B C]
  [IsScalarTower R (A ⊗[R] B) C] [IsScalarTower A (A ⊗[R] B) C] [IsScalarTower B (A ⊗[R] B) C]
  [IsScalarTower R A C] [IsScalarTower R B C] [Algebra.WeaklyEtale (A ⊗[R] B) C]

/-- **The ring-theoretic content of Stacks 09DL.** If `A` and `B` are Tor independent over `R` and
`A ⊗_R B → C` is weakly étale, every cone `E_C` of `L_{B/R} ⊗^𝐋_B C ⟶ L_{C/R} ⟶ L_{C/A}` is zero:
its cohomology is that of the object `E` of the nine diagram of `R → A, R → B` tensored up to `C`,
and `E = 0` by Stacks 09DA. -/
theorem isZero_cone_fundamentalMor_of_torIndependent
    (hTor : RingTheory.TorIndependence.TorIndependent R A B)
    {EC : DerivedCategory (ModuleCat.{u} C)}
    {b' : cotangentComplexDerived.{u, u} A (CommAlgCat.of A C) ⟶ EC}
    {e' : EC ⟶ (fundamentalVertex₁.{u, u, u + 1, u + 1} R B C)⟦(1 : ℤ)⟧}
    (hC : Triangle.mk (fundamentalMor₁.{u} R B C ≫ fundamentalMor₂.{u} R A C) b' e' ∈
      distTriang (DerivedCategory (ModuleCat.{u} C))) :
    IsZero EC := by
  rw [DerivedCategory.isZero_iff_forall_isZero_homology]
  intro i
  obtain ⟨φ⟩ := nonempty_homology_cone_iso_extendScalars_tensorProduct R A B C
    (canonicalTensorProductNineDiagram_rightColumn R A B) hC i
  exact ((ModuleCat.extendScalars.{u, u, u} (algebraMap (A ⊗[R] B) C)).map_isZero
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} (A ⊗[R] B)) i).map_isZero
      (isZero_canonicalTensorProductNineDiagram_upperRight_of_torIndependent R A B hTor))).of_iso φ

end NineDiagram

section Transport

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe v

variable {R' A' B' C' : Type v} [CommRing R'] [CommRing A'] [CommRing B'] [CommRing C']
  [Algebra R' A'] [Algebra R' B'] [Algebra R' C'] [Algebra A' C'] [Algebra B' C']
  [IsScalarTower R' A' C'] [IsScalarTower R' B' C']
  {R A B C : Type v} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra R A] [Algebra R B]

/-- **The ring-theoretic content of Stacks 09DL, transported along isomorphisms of rings.** Let
`R' → A', B' → C'` be a commutative diagram of rings isomorphic, by `ρ`, to `R → A, B → C`, where
`A` and `B` are Tor independent over `R` and `C` is weakly étale over `A ⊗_R B` along `φ`. Then
every cone of `L_{B'/R'} ⊗^𝐋_{B'} C' ⟶ L_{C'/R'} ⟶ L_{C'/A'}` is zero. -/
theorem isZero_cone_fundamentalMor_of_ringEquiv_of_torIndependent (φ : A ⊗[R] B →+* C)
    (hW : @Algebra.WeaklyEtale _ _ _ _ φ.toAlgebra)
    (ρR : R' ≃+* R) (ρA : A' ≃+* A) (ρB : B' ≃+* B) (ρC : C' ≃+* C)
    (hA : ∀ r, ρA (algebraMap R' A' r) = algebraMap R A (ρR r))
    (hB : ∀ r, ρB (algebraMap R' B' r) = algebraMap R B (ρR r))
    (hAC : ∀ a, ρC (algebraMap A' C' a) = φ (ρA a ⊗ₜ[R] 1))
    (hBC : ∀ b, ρC (algebraMap B' C' b) = φ (1 ⊗ₜ[R] ρB b))
    (hTor : RingTheory.TorIndependence.TorIndependent R A B)
    {EC : DerivedCategory (ModuleCat.{v} C')}
    {b' : cotangentComplexDerived.{v, v} A' (CommAlgCat.of A' C') ⟶ EC}
    {e' : EC ⟶ (fundamentalVertex₁.{v, v, v + 1, v + 1} R' B' C')⟦(1 : ℤ)⟧}
    (hC : Triangle.mk (fundamentalMor₁.{v} R' B' C' ≫ fundamentalMor₂.{v} R' A' C') b' e' ∈
      distTriang (DerivedCategory (ModuleCat.{v} C'))) :
    IsZero EC := by
  let ψ : A' ⊗[R'] B' →ₐ[R'] C' := Algebra.TensorProduct.lift (IsScalarTower.toAlgHom R' A' C')
    (IsScalarTower.toAlgHom R' B' C') fun _ _ => Commute.all _ _
  have hψ : ∀ a b, ψ (a ⊗ₜ[R'] b) = algebraMap A' C' a * algebraMap B' C' b :=
    fun _ _ => Algebra.TensorProduct.lift_tmul ..
  let : Algebra (A' ⊗[R'] B') C' := ψ.toRingHom.toAlgebra
  have : IsScalarTower R' (A' ⊗[R'] B') C' :=
    IsScalarTower.of_algebraMap_eq fun r => (ψ.commutes r).symm
  have : IsScalarTower A' (A' ⊗[R'] B') C' := IsScalarTower.of_algebraMap_eq fun a => by
    change _ = ψ (a ⊗ₜ[R'] 1)
    simp [hψ]
  have : IsScalarTower B' (A' ⊗[R'] B') C' := IsScalarTower.of_algebraMap_eq fun b => by
    change _ = ψ (1 ⊗ₜ[R'] b)
    simp [hψ]
  have hτ : ∀ t, ρC (algebraMap (A' ⊗[R'] B') C' t) =
      φ (TorChangeOfRings.equivTensorProductRingEquiv ρR ρA ρB hA hB t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      change ρC (ψ (a ⊗ₜ[R'] b)) =
        φ (TorChangeOfRings.equivTensorProductMap ρR ρA ρB hA hB (a ⊗ₜ[R'] b))
      rw [TorChangeOfRings.equivTensorProductMap_tmul, hψ, map_mul]
      rw [hAC, hBC, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  have : Algebra.WeaklyEtale (A' ⊗[R'] B') C' :=
    @Algebra.WeaklyEtale.of_ringEquiv _ _ _ _ _ _ _ _ φ.toAlgebra _ hW
      (TorChangeOfRings.equivTensorProductRingEquiv ρR ρA ρB hA hB) ρC hτ
  have hTor' : RingTheory.TorIndependence.TorIndependent R' A' B' :=
    (RingTheory.TorIndependence.torIndependent_congr_universe.{v, 0} ρR ρA ρB hA hB).1 hTor
  exact isZero_cone_fundamentalMor_of_torIndependent R' A' B' C' hTor' hC

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

attribute [local instance high] hasPullback_presheaf_fibreProductCornerCohomology

/-- **Stacks 09DL at a geometric point.** For a cartesian square of algebraic spaces with `X` and
`Y` Tor independent over `Z`, the derived stalk at every geometric point of `W` of an object `E`
fitting into the upper right corner of the diagram of Stacks 09DK is zero. -/
theorem isZero_derivedStalk_upperRightCorner_of_torIndependent (hpb : IsPullback p q f g)
    (hTor : TorIndependent X.2 Y.2 Z.2 f.hom g.hom)
    (E : Triangulated.UpperRightCorner (transitivityUnit p f) (transitivityCounit p f)
      (fibreProductColumnUnit hpb.w) (fibreProductColumnCounit hpb.w))
    (w : GeometricPoint B S hS W.1) :
    IsZero ((derivedStalk B S hS W w).obj E.obj) := by
  obtain ⟨φ₀, ψ₀, hφ₀, hψ₀, hT₀⟩ := hTor (geometricPointMap p.hom w) (geometricPointMap q.hom w)
    (congrArg (fun k : W ⟶ Z => geometricPointMap k.hom w) hpb.w)
  obtain rfl := eq_etaleLocalRingMap X.2 f.hom _ hφ₀
  obtain rfl := eq_etaleLocalRingMap Y.2 g.hom _ hψ₀
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
  exact CommAlgCat.isZero_cone_fundamentalMor_of_ringEquiv_of_torIndependent φ hW
    (towerBaseStalkEquiv B S hS hpb.w w) (liftedBaseRingStalkEquiv B S hS p w)
    (inverseImageStalkEquiv B S hS q w) (smallEtaleStructureSheafULiftStalkEquiv B S hS W w)
    (columnBaseMap_stalk_apply hpb.w w) (towerBaseMap_stalk_apply hpb.w w)
    (fun a => (liftedStructureMap_stalk_apply p w a).trans
      (RingHom.congr_fun hφA (liftedBaseRingStalkEquiv B S hS p w a)).symm)
    (fun b => (fSharpInverseImageULift_stalk_apply w b).trans
      (RingHom.congr_fun hφB (inverseImageStalkEquiv B S hS q w b)).symm) hT₀ hC

/-- **Stacks 09DL, first assertion, for a cartesian square.** If `X` and `Y` are Tor independent
over `Z`, every object `E` fitting into the upper right corner of the diagram of Stacks 09DK is
zero. -/
theorem isZero_upperRightCorner_of_torIndependent (hpb : IsPullback p q f g)
    (hTor : TorIndependent X.2 Y.2 Z.2 f.hom g.hom)
    (E : Triangulated.UpperRightCorner (transitivityUnit p f) (transitivityCounit p f)
      (fibreProductColumnUnit hpb.w) (fibreProductColumnCounit hpb.w)) :
    IsZero E.obj := by
  rw [DerivedCategory.isZero_iff_forall_isZero_homology]
  exact fun i => isZero_homology_of_forall_derivedStalk B S hS W E.obj i fun w =>
    (DerivedCategory.homologyFunctor _ i).map_isZero
      (isZero_derivedStalk_upperRightCorner_of_torIndependent hpb hTor E w)

/-- **Stacks 09DL, second assertion, for a cartesian square.** If `X` and `Y` are Tor independent
over `Z`, the canonical map `Lp^*L_{X/Z} ⊕ Lq^*L_{Y/Z} ⟶ L_{W/Z}` is an isomorphism: its cone is
an object fitting into the upper right corner of the diagram of Stacks 09DK, hence zero. -/
theorem isIso_fibreProductBiprodMap_of_torIndependent (hpb : IsPullback p q f g)
    (hTor : TorIndependent X.2 Y.2 Z.2 f.hom g.hom) :
    IsIso (fibreProductBiprodMap hpb.w) := by
  obtain ⟨_, h₁⟩ := exists_distTriang_transitivity p f
  obtain ⟨_, h₂⟩ := exists_distTriang_fibreProductColumn hpb.w
  obtain ⟨_, _, _, hc⟩ := distinguished_cocone_triangle (fibreProductBiprodMap hpb.w)
  exact (Triangle.isZero₃_iff_isIso₁ _ hc).1 (isZero_upperRightCorner_of_torIndependent hpb hTor
    (Triangulated.UpperRightCorner.ofBiprodCone h₁ h₂ hc))

/-- **Stacks 09DL.** Let `X ⟶ Z` and `Y ⟶ Z` be morphisms of algebraic spaces over `S`, and let
`W = X ×_Z Y` with projections `p` and `q`. If `X` and `Y` are Tor independent over `Z`, then the
object `E` of Stacks 09DK, i.e. any object fitting into the upper right corner of its diagram, is
zero, and the canonical map `Lp^*L_{X/Z} ⊕ Lq^*L_{Y/Z} ⟶ L_{W/Z}` is an isomorphism, so that
`L_{X ×_Z Y/Z} ≅ Lp^*L_{X/Z} ⊕ Lq^*L_{Y/Z}`. -/
@[stacks 09DL]
theorem fiberProduct_cotangentComplex_of_torIndependent (f : X ⟶ Z) (g : Y ⟶ Z)
    (hTor : TorIndependent X.2 Y.2 Z.2 f.hom g.hom) :
    (∀ E : Triangulated.UpperRightCorner (transitivityUnit (ObjectProperty.homMk (pullback.fst
        f.hom g.hom) : (AlgebraicSpaces.fiberProduct B S hS f g) ⟶ X) f) (transitivityCounit
            (ObjectProperty.homMk (pullback.fst f.hom g.hom) : (AlgebraicSpaces.fiberProduct B S hS
                f g) ⟶ X) f)
      (fibreProductColumnUnit (AlgebraicSpaces.isPullback_fiberProduct B S hS f g).w)
      (fibreProductColumnCounit (AlgebraicSpaces.isPullback_fiberProduct B S hS f g).w),
      IsZero E.obj) ∧
    IsIso (fibreProductBiprodMap (AlgebraicSpaces.isPullback_fiberProduct B S hS f g).w) :=
  ⟨isZero_upperRightCorner_of_torIndependent
      (AlgebraicSpaces.isPullback_fiberProduct B S hS f g) hTor,
    isIso_fibreProductBiprodMap_of_torIndependent
      (AlgebraicSpaces.isPullback_fiberProduct B S hS f g) hTor⟩

end AlgebraicGeometry.Space

end
