module

public import StacksFrontier.AlgebraicGeometry.DeRham.KunnethDegreewise

/-!
# The degreewise de Rham Künneth isomorphism is the wedge product of pulled-back forms

Let `a : X ⟶ S` and `b : Y ⟶ S` be morphisms of schemes and let `W = X ×_S Y`. The degreewise
isomorphism `Tot(Ω^•_{X/S} ⊠ Ω^•_{Y/S})^n ≅ Ω^n_{W/S}` of
`StacksFrontier.AlgebraicGeometry.DeRham.KunnethDegreewise` is assembled from the splitting of
`Ω_{W/S}`, the Künneth decomposition of an exterior power of a direct sum, and the comparison of
[Stacks, Tag 01CI]. This file identifies its restriction to the `(p, q)` summand with the single
morphism one expects:

`ω ⊗ η ↦ pr₁^*ω ∧ pr₂^*η`,

where `pr₁^*` and `pr₂^*` are the canonical maps `pr_i^*Ω^p ⟶ Ω^p_{W/S}` on relative differential
forms of [Stacks, Tag 0FL5] and `∧` is multiplication in the exterior algebra of `Ω_{W/S}`.

This is the shape in which the compatibility of the degreewise isomorphism with the de Rham
differentials is to be checked: the graded Leibniz rule
`AlgebraicGeometry.SheafOfModules.d_formProduct` applies to a product of two local differential
forms on `W`, and the two factors here are pullbacks of forms from `X` and from `Y`.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.deRhamBoxLeftMap` and
  `AlgebraicGeometry.Scheme.Hom.deRhamBoxRightMap`: the two canonical maps
  `pr₁^*Ω_{X/S} ⟶ Ω_{W/S}` and `pr₂^*Ω_{Y/S} ⟶ Ω_{W/S}` of [Stacks, Tag 01UV], the two legs of
  the splitting of [Stacks, Tag 01V1].

## Main results

* `SheafOfModules.prodWedgeHom_unit`: the wedge-product component morphism on an arbitrary local
  pure tensor is the product of the images of the two factors under the functorial maps on
  exterior powers.
* `SheafOfModules.prodWedgeHom_comp_exteriorPowerMap` and
  `SheafOfModules.prodWedgeHomOfEq_comp_exteriorPowerMap`: postcomposing the wedge-product
  component with the functorial map of a morphism `e` of the target composes `e` onto each of the
  two legs.
* `AlgebraicGeometry.Scheme.Hom.biproduct_ι_comp_deRhamBoxModuleIso_hom`: **on the `(p, q)`
  summand the degreewise Künneth isomorphism of sheaves of modules is the wedge product of the
  canonical maps on forms of the two projections.**
* `AlgebraicGeometry.Scheme.Hom.ιTotal_comp_deRhamBoxTotalDegreeIso_wedge`: the same statement
  for the degreewise isomorphism of [Stacks, Tag 0FMA] in the category of finite-order
  differential operators.

## Implementation notes

Everything is an identity of morphisms, with no section formula: the Künneth isomorphism of
`AlgebraicGeometry.Scheme.Hom.deRhamBoxModuleIso` is a chain of four named isomorphisms, each of
which is a `CategoryTheory.Limits.Sigma.desc`, a reindexing of a coproduct, or a functorial
exterior power, so the restriction to one summand is computed by the universal property of the
coproduct together with multiplicativity of the functorial map on exterior powers. The last of
those is `SheafOfModules.GradedAlgebra.mulSheaf_comp_eq_iff` in the form
`SheafOfModules.GradedAlgebra.UnitalHom.map_mul`, used through the section formula
`SheafOfModules.prodWedgeHom_unit`.

`AlgebraicGeometry.Scheme.Modules` is a semireducible definition whose sheaf of rings is written
at the `CategoryTheory.Sheaf.toRingCat` spelling in the Künneth decomposition, so `rewrite` and
`simp` fail to build a motive for the associativity steps and the reassociations are performed in
term mode, as in `StacksFrontier.AlgebraicGeometry.DeRham.KunnethDegreewise`. For the same reason
the
two biproduct injections of the splitting are left to unification rather than written out: at the
`toRingCat` spelling `CategoryTheory.Limits.HasZeroMorphisms` is not synthesizable, so
`CategoryTheory.Limits.biprod.inl` cannot be elaborated there.

## References

* [Stacks Project, Tag 0FMA](https://stacks.math.columbia.edu/tag/0FMA)
* [Stacks Project, Tag 01V1](https://stacks.math.columbia.edu/tag/01V1)
* [Stacks Project, Tag 01CI](https://stacks.math.columbia.edu/tag/01CI)
* [Stacks Project, Tag 0FL5](https://stacks.math.columbia.edu/tag/0FL5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Sheaf CategoryTheory.Limits TopologicalSpace
open scoped TensorProduct

universe u

namespace SheafOfModules

variable {X : TopCat.{u}} {Osharp : Sheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u}}
  {F G H H' : SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}
  (AF : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X) F)
  (AG : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X) G)
  (A : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X) H)
  (A' : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X) H')

/-- **The wedge-product component morphism on an arbitrary local pure tensor**: it multiplies the
images of the two factors under the functorial maps `⋀ᵖF ⟶ ⋀ᵖH` and `⋀^qG ⟶ ⋀^qH`. -/
theorem prodWedgeHom_unit (iF : F ⟶ H) (iG : G ⟶ H) (p q : ℕ) (U : (Opens ↥X)ᵒᵖ)
    (ξ : (AF.exteriorPower p).val.obj U) (η : (AG.exteriorPower q).val.obj U) :
    (prodWedgeHom AF AG A iF iG p q).val.app U
        ((PresheafOfModules.tensorSheafUnit (AF.exteriorPower p) (AG.exteriorPower q)).app U
          (ξ ⊗ₜ η)) =
      (A.exterior.mul (p : ℤ) (q : ℤ)).app U
        ((AF.exterior_isExteriorAlgebra.pieceMap A.exterior_isExteriorAlgebra iF
          (p : ℤ)).val.app U ξ)
        ((AG.exterior_isExteriorAlgebra.pieceMap A.exterior_isExteriorAlgebra iG
          (q : ℤ)).val.app U η) :=
  (congrArg (fun z => (GradedAlgebra.mulSheaf A.exterior (p : ℤ) (q : ℤ)).val.app U z)
      (Stacks.TensorSheafWorld.tensorSheafBifunctor_map_val_app_tensorSheafUnit Osharp
        (AF.exteriorPower p) (AG.exteriorPower q)
        ((AF.exterior_isExteriorAlgebra.map A.exterior_isExteriorAlgebra iF).app (p : ℤ))
        ((AG.exterior_isExteriorAlgebra.map A.exterior_isExteriorAlgebra iG).app (q : ℤ))
        U ξ η)).trans
    (GradedAlgebra.mulSheaf_unit A.exterior (p : ℤ) (q : ℤ) U _ _)

/-- The comparison morphism out of the direct sum of the Künneth summands, restricted to the
summand of index `(p, q)`, is the wedge-product component in that bidegree. -/
theorem ι_comp_exteriorPowerProdHom (iF : F ⟶ H) (iG : G ⟶ H) (n : ℕ)
    (i : ULift.{u} {pq : ℕ × ℕ // pq.1 + pq.2 = n})
    [HasCoproduct (exteriorPowerProdSummand AF AG n)] :
    Sigma.ι (exteriorPowerProdSummand AF AG n) i ≫ exteriorPowerProdHom AF AG A iF iG n =
      prodWedgeHomOfEq AF AG A iF iG i.down.1.1 i.down.1.2 n i.down.2 :=
  Sigma.ι_comp_desc _ i

/-- **Postcomposing the wedge-product component with the functorial map of a morphism `e` of the
target composes `e` onto each of the two legs**: the functorial map on exterior powers is
multiplicative, so wedging and then mapping is mapping each factor and then wedging. -/
theorem prodWedgeHom_comp_exteriorPowerMap (iF : F ⟶ H) (iG : G ⟶ H) (e : H ⟶ H') (p q : ℕ) :
    prodWedgeHom AF AG A iF iG p q ≫
        TensorExteriorSymmetricAlgebras.exteriorPowerMap A A' e ((p + q : ℕ) : ℤ) =
      prodWedgeHom AF AG A' (iF ≫ e) (iG ≫ e) p q := by
  refine PresheafOfModules.tensorSheaf_hom_ext (Osharp := Osharp)
    (F := AF.exteriorPower p) (G := AG.exteriorPower q)
    (Q := A'.exteriorPower (p + q)) fun U ξ η => ?_
  refine Eq.trans (congrArg
    ((A.exterior_isExteriorAlgebra.pieceMap A'.exterior_isExteriorAlgebra e
      ((p + q : ℕ) : ℤ)).val.app U) (prodWedgeHom_unit AF AG A iF iG p q U ξ η)) ?_
  refine Eq.trans ((A.exterior_isExteriorAlgebra.map A'.exterior_isExteriorAlgebra e).map_mul
    (p : ℤ) (q : ℤ) U _ _) ?_
  refine Eq.trans ?_ (prodWedgeHom_unit AF AG A' (iF ≫ e) (iG ≫ e) p q U ξ η).symm
  exact congrArg₂ (fun y z => (A'.exterior.mul (p : ℤ) (q : ℤ)).app U y z)
    (congrArg (fun φ : AF.exteriorPower p ⟶ A'.exteriorPower p => φ.val.app U ξ)
      (AF.exterior_isExteriorAlgebra.pieceMap_comp A.exterior_isExteriorAlgebra
        A'.exterior_isExteriorAlgebra iF e (p : ℤ)).symm)
    (congrArg (fun φ : AG.exteriorPower q ⟶ A'.exteriorPower q => φ.val.app U η)
      (AG.exterior_isExteriorAlgebra.pieceMap_comp A.exterior_isExteriorAlgebra
        A'.exterior_isExteriorAlgebra iG e (q : ℤ)).symm)

/-- `SheafOfModules.prodWedgeHom_comp_exteriorPowerMap` with the target transported along
`p + q = n`. -/
theorem prodWedgeHomOfEq_comp_exteriorPowerMap (iF : F ⟶ H) (iG : G ⟶ H) (e : H ⟶ H')
    (p q n : ℕ) (h : p + q = n) :
    prodWedgeHomOfEq AF AG A iF iG p q n h ≫
        TensorExteriorSymmetricAlgebras.exteriorPowerMap A A' e (n : ℤ) =
      prodWedgeHomOfEq AF AG A' (iF ≫ e) (iG ≫ e) p q n h := by
  subst h
  rw [prodWedgeHomOfEq_rfl, prodWedgeHomOfEq_rfl]
  exact prodWedgeHom_comp_exteriorPowerMap AF AG A A' iF iG e p q

end SheafOfModules

namespace AlgebraicGeometry

attribute [local instance] hasColimits_sheafOfModules_toRingCat
attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace Scheme.Hom

open FiniteOrderDifferentialOperatorCategory

variable {X Y S : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)

/-- The canonical map `pr₁^*Ω_{X/S} ⟶ Ω_{X ×_S Y/S}` of [Stacks, Tag 01UV] attached to the first
projection, read over the base `S`. It is the first leg of the splitting of [Stacks, Tag 01V1]. -/
noncomputable abbrev deRhamBoxLeftMap :
    (Scheme.Modules.pullback (pullback.fst a b)).obj (relativeDifferentials a) ⟶
      relativeDifferentials (pullback.fst a b ≫ a) :=
  relativeDifferentialsMap (pullback.fst a b) a (pullback.fst a b ≫ a) (𝟙 S)
    (Category.comp_id (pullback.fst a b ≫ a)).symm

/-- The canonical map `pr₂^*Ω_{Y/S} ⟶ Ω_{X ×_S Y/S}` of [Stacks, Tag 01UV] attached to the second
projection, read over the base `S`. It is the second leg of the splitting of
[Stacks, Tag 01V1]. -/
noncomputable abbrev deRhamBoxRightMap :
    (Scheme.Modules.pullback (pullback.snd a b)).obj (relativeDifferentials b) ⟶
      relativeDifferentials (pullback.fst a b ≫ a) :=
  relativeDifferentialsMap (pullback.snd a b) b (pullback.fst a b ≫ a) (𝟙 S)
    ((IsPullback.of_hasPullback a b).w.symm.trans
      (Category.comp_id (pullback.fst a b ≫ a)).symm)

/-- The splitting isomorphism of [Stacks, Tag 01V1] restricted to the first summand is the
canonical map of the first projection. -/
theorem biprod_inl_comp_deRhamBoxSplitIso_hom :
    biprod.inl ≫ (deRhamBoxSplitIso a b).hom = deRhamBoxLeftMap a b :=
  biprod.inl_desc _ _

/-- The splitting isomorphism of [Stacks, Tag 01V1] restricted to the second summand is the
canonical map of the second projection. -/
theorem biprod_inr_comp_deRhamBoxSplitIso_hom :
    biprod.inr ≫ (deRhamBoxSplitIso a b).hom = deRhamBoxRightMap a b :=
  biprod.inr_desc _ _

/-- The degreewise Künneth isomorphism of sheaves of modules, written as the chain of its four
named factors. -/
theorem deRhamBoxModuleIso_eq (n : ℕ) :
    deRhamBoxModuleIso a b n =
      biproduct.isoCoproduct (fun k => (deRhamBoxSummand a b n k).module) ≪≫
        Sigma.whiskerEquiv (g := SheafOfModules.exteriorPowerProdSummand
            (deRhamBoxAlgebrasLeft a b) (deRhamBoxAlgebrasRight a b) n)
          (Equiv.ulift (α := deRhamBoxIndex n)).symm (fun j => deRhamBoxSummandIso a b n j) ≪≫
        @SheafOfModules.exteriorPowerBiprodIso _ _ _ _
          (hasBinaryBiproduct_sheafOfModules_toRingCat (pullback a b) _ _)
          (deRhamBoxAlgebrasLeft a b) (deRhamBoxAlgebrasRight a b)
          (deRhamBoxAlgebrasSum a b) n ≪≫
        (Scheme.Modules.exteriorPowerFunctor (pullback a b) (n : ℤ)).mapIso
          (deRhamBoxSplitIso a b) :=
  rfl

/-- **On the `(p, q)` summand the degreewise Künneth isomorphism of sheaves of modules is the
wedge product of the canonical maps on forms of the two projections**: it carries the summand
`pr₁^*Ω^p_{X/S} ⊗ pr₂^*Ω^q_{Y/S}` into `Ω^{p+q}_{X ×_S Y/S}` by applying the canonical map of
[Stacks, Tag 0FL5] to each factor and multiplying in the exterior algebra of `Ω_{X ×_S Y/S}`. -/
theorem biproduct_ι_comp_deRhamBoxModuleIso_hom (n : ℕ) (j : deRhamBoxIndex n) :
    biproduct.ι (fun k => (deRhamBoxSummand a b n k).module) j ≫
        (deRhamBoxModuleIso a b n).hom =
      (deRhamBoxSummandIso a b n j).inv ≫
        SheafOfModules.prodWedgeHomOfEq (deRhamBoxAlgebrasLeft a b) (deRhamBoxAlgebrasRight a b)
          (deRhamAlgebras (pullback.fst a b ≫ a)) (deRhamBoxLeftMap a b) (deRhamBoxRightMap a b)
          j.1.1 j.1.2 n j.2 := by
  have h1 : biproduct.ι (fun k => (deRhamBoxSummand a b n k).module) j ≫
        (biproduct.isoCoproduct (fun k => (deRhamBoxSummand a b n k).module)).hom =
      Sigma.ι (fun k => (deRhamBoxSummand a b n k).module) j := by
    rw [biproduct.isoCoproduct_hom, biproduct.ι_desc]
  have h2 : Sigma.ι (fun k => (deRhamBoxSummand a b n k).module) j ≫
        (Sigma.whiskerEquiv (g := SheafOfModules.exteriorPowerProdSummand
            (deRhamBoxAlgebrasLeft a b) (deRhamBoxAlgebrasRight a b) n)
          (Equiv.ulift (α := deRhamBoxIndex n)).symm
          (fun j => deRhamBoxSummandIso a b n j)).hom =
      (deRhamBoxSummandIso a b n j).inv ≫
        Sigma.ι (SheafOfModules.exteriorPowerProdSummand (deRhamBoxAlgebrasLeft a b)
          (deRhamBoxAlgebrasRight a b) n) (ULift.up j) :=
    Sigma.ι_comp_map' _ _ j
  rw [deRhamBoxModuleIso_eq]
  erw [Iso.trans_hom, Iso.trans_hom, Iso.trans_hom, Functor.mapIso_hom,
    ← Category.assoc, h1, ← Category.assoc, h2, Category.assoc]
  exact congrArg _ <|
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun z => z ≫ SheafOfModules.TensorExteriorSymmetricAlgebras.exteriorPowerMap
            (deRhamBoxAlgebrasSum a b) (deRhamAlgebras (pullback.fst a b ≫ a))
            (deRhamBoxSplitIso a b).hom (n : ℤ))
          (SheafOfModules.ι_comp_exteriorPowerProdHom (deRhamBoxAlgebrasLeft a b)
            (deRhamBoxAlgebrasRight a b) (deRhamBoxAlgebrasSum a b) _ _ n
            (ULift.up j))).trans
        ((SheafOfModules.prodWedgeHomOfEq_comp_exteriorPowerMap (deRhamBoxAlgebrasLeft a b)
            (deRhamBoxAlgebrasRight a b) (deRhamBoxAlgebrasSum a b)
            (deRhamAlgebras (pullback.fst a b ≫ a)) _ _
            (deRhamBoxSplitIso a b).hom j.1.1 j.1.2 n j.2).trans
          (congrArg₂ (fun u v => SheafOfModules.prodWedgeHomOfEq (deRhamBoxAlgebrasLeft a b)
              (deRhamBoxAlgebrasRight a b) (deRhamAlgebras (pullback.fst a b ≫ a)) u v
              j.1.1 j.1.2 n j.2)
            (biprod_inl_comp_deRhamBoxSplitIso_hom a b)
            (biprod_inr_comp_deRhamBoxSplitIso_hom a b))))

/-- **On the `(p, q)` summand of the total complex the degreewise isomorphism of
[Stacks, Tag 0FMA] is the wedge product of the canonical maps on forms of the two projections**,
read as a differential operator of order zero. This is the identification against which the
graded Leibniz rule is to be applied. -/
theorem ιTotal_comp_deRhamBoxTotalDegreeIso_wedge (n : ℕ) (j : deRhamBoxIndex n) :
    (deRhamBoxDoubleComplex a b).ιTotal (ComplexShape.up ℕ) j.1.1 j.1.2 n j.2 ≫
        (deRhamBoxTotalDegreeIso a b n).hom =
      homOrderZeroAddMonoidHom _ _
        ((deRhamBoxSummandIso a b n j).inv ≫
          SheafOfModules.prodWedgeHomOfEq (deRhamBoxAlgebrasLeft a b)
            (deRhamBoxAlgebrasRight a b) (deRhamAlgebras (pullback.fst a b ≫ a))
            (deRhamBoxLeftMap a b) (deRhamBoxRightMap a b) j.1.1 j.1.2 n j.2) :=
  (ιTotal_comp_deRhamBoxTotalDegreeIso_hom a b n j).trans
    (congrArg (fun z => homOrderZeroAddMonoidHom (deRhamBoxSummand a b n j)
        (deRhamDiffOpTerm (pullback.fst a b ≫ a) n) z)
      (biproduct_ι_comp_deRhamBoxModuleIso_hom a b n j))

end Scheme.Hom

end AlgebraicGeometry

end
