module

public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeWeil.Pullback
public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeWeil.Algebra
public import StacksFrontier.AlgebraicGeometry.DeRham.FirstChernClass.HodgeCupProduct
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.RelativeCupProductOnCohomology
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.CupProductAndDerivedPushforward
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.NaiveCupProductSummand
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.NaiveCupProductOnSections
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.GlobalCupProductShift
public import StacksFrontier.AlgebraicGeometry.DeRham.DifferentialGradedAlgebra.ActionTotalComplex
public import StacksFrontier.Algebra.Homology.Embedding.UpNatZero

/-!
# Pullback on Hodge cohomology is a map of graded algebras

Consider a commutative square of schemes

```
X' --g'--> X
|f'        |f
v          v
S' --g---> S
```

and let `g₀ : (X', f'⁻¹𝒪_{S'}) ⟶ (X, f⁻¹𝒪_S)` be its morphism of ringed spaces. Section 50.5
(Tag 0FM4) defines the pullback maps `g'^* : H^q(X, Ω^p_{X/S}) ⟶ H^q(X', Ω^p_{X'/S'})` and the cup
product on Hodge cohomology, the cup product of Cohomology, Section 0FKU combined with the wedge
product of forms, and records that pullback is compatible with the cup product:

`g'^*(ξ ∪ ζ) = g'^*ξ ∪ g'^*ζ`, and `g'^*1 = 1`.

Hence the induced map `H^*_{Hodge}(X/S) ⟶ H^*_{Hodge}(X'/S')` is a homomorphism of graded rings;
for morphisms of `S`-schemes, with a ring `k` acting through a ring map `k ⟶ Γ(S, 𝒪_S)`, it is a
homomorphism of graded `k`-algebras, and it is functorial. For `S = Spec k` this is datum (D1) of
Weil cohomology theories (Section 0FID) for Hodge cohomology, as Remark 0FWE uses it.

The proof is the source's. The canonical map `Ω^p_{X/S}[0] ⟶ Rg₀_*Ω^p_{X'/S'}[0]` is
multiplicative: on local sections, pulling back forms is multiplicative, and the passage from the
naive cup product to the relative cup product of Tag 0B68 is Tag 0FP3. The relative cup product
induces the cup product on cohomology through the Leray identification
`H^n(X, Rg₀_* -) = H^n(X', -)`, which is how the pullback is defined.

## Main definitions

* `Stacks.HodgeWeil.singleIntMultiplication`: the multiplication `Tot(F[0] ⊗ G[0]) ⟶ H[0]` of
  `ℤ`-indexed complexes concentrated in degree `0` induced by a morphism `F ⊗ G ⟶ H`.
* `Stacks.HodgeWeil.formsSingleWedge`: the wedge product
  `Tot(Ω^p_{X/S}[0] ⊗ Ω^{p'}_{X/S}[0]) ⟶ Ω^{p+p'}_{X/S}[0]`.
* `Stacks.HodgeWeil.formsComparisonQ`: the canonical map `Ω^p_{X/S}[0] ⟶ Rg₀_*Ω^p_{X'/S'}[0]`.
* `Stacks.HodgeWeil.hodgePiecePullback` and `Stacks.HodgeWeil.hodgeAlgebraPullback`: the
  pullback on `H^n_{Hodge}` and the ring homomorphism on `H^*_{Hodge}`.
* `Stacks.HodgeWeil.hodgeAlgebraPullbackAlgHom`: the pullback as a homomorphism of
  `k`-algebras, for compatible ring maps from `k`.
* `Stacks.HodgeWeil.hodgeScalars` and `Stacks.HodgeWeil.hodgeAlgebraPullbackOverBase`: the
  `k`-structure of an `S`-scheme through `k ⟶ Γ(S, 𝒪_S)`, and the pullback along a morphism of
  `S`-schemes as a homomorphism of `k`-algebras.

## Main results

* `Stacks.HodgeWeil.hodgeComponentCup_eq_totalCupPairing`: the cup product of Section 0FKU on
  `H^q(X, Ω^p)` through the `ℤ`-indexed complexes concentrated in degree `0`.
* `Stacks.HodgeWeil.formsSingleWedge_comp_formsSinglePushforward`: **the canonical map of forms
  is multiplicative**, as a morphism of complexes.
* `Stacks.HodgeWeil.formsComparisonQ_multiplicative`: the same in the derived category.
* `Stacks.HodgeWeil.hodgePullback_hodgeCohomologyCup`: **`g'^*(ξ ∪ ζ) = g'^*ξ ∪ g'^*ζ`.**
* `Stacks.HodgeWeil.hodgePullback_hodgeOne`: **`g'^*1 = 1`.**
* `Stacks.HodgeWeil.hodgePiecePullback_mul`, `Stacks.HodgeWeil.hodgeAlgebraPullback_id` and
  `Stacks.HodgeWeil.hodgeAlgebraPullback_comp`: the pullback on `H^*_{Hodge}` is multiplicative
  and functorial.
* `Stacks.HodgeWeil.hodgeAlgebraPullbackOverBase_id`,
  `Stacks.HodgeWeil.hodgeAlgebraPullbackOverBase_comp` and
  `Stacks.HodgeWeil.hodgeAlgebraPullbackOverBase_mem_hodgeGrade`: for `S`-schemes the pullbacks
  are homomorphisms of graded `k`-algebras, functorial in the morphism.

## Implementation notes

The pullback is built on the cohomology of `Ω^p[0]` read as a `ℤ`-indexed complex concentrated
in degree `0`, while the cup product `AlgebraicGeometry.SheafOfModules.hodgeComponentCup` is
built on the extension by zero of the `ℕ`-indexed one. The two complexes are identified by
`HomologicalComplex.extendSingleIso`, and `Stacks.HodgeWeil.singleIntMultiplication` is the
multiplication of the latter read on the former.

The same objects are written at several definitionally equal spellings, and a statement
must use the spelling its instances are found at: complexes of `f⁻¹𝒪_S`-modules are written as
`Stacks.HodgeWeil.formsSingleModules` where the tensor product of sheaves of modules is formed,
and the algebras of differential forms as `Stacks.HodgeWeil.formsAlgebras`, typed through the
structure map `f⁻¹𝒪_S ⟶ 𝒪_X`, wherever the Hodge cohomology groups are.

## References

* [Stacks Project, Tag 0FM4](https://stacks.math.columbia.edu/tag/0FM4)
* [Stacks Project, Tag 0FP3](https://stacks.math.columbia.edu/tag/0FP3)
* [Stacks Project, Tag 0B68](https://stacks.math.columbia.edu/tag/0B68)
* [Stacks Project, Section 0FKU](https://stacks.math.columbia.edu/tag/0FKU)
* [Stacks Project, Remark 0FWE](https://stacks.math.columbia.edu/tag/0FWE)
* [Stacks Project, Section 0FID](https://stacks.math.columbia.edu/tag/0FID)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open ComplexShape
open Stacks.SheafOfModules.Tensor (sheafTensor)
open Stacks.Cohomology.GlobalKunneth (baseRing baseSections)
open Stacks.Cohomology.DerivedGlobalCupProduct (cohomologyModule cohomologyMap totalCupPairing)
open AlgebraicGeometry.SheafOfModules (hodgeCohomologyComponent underlyingRingSheaf
  singleNat singleMultiplication multiplicationInt hodgeComponentCup hodgeComponentIso
  toHodgeComponentBase ofHodgeComponentBase baseRingedSpace FormsMultiplication
  moduleOfDifferentials deRhamTerm reindexHodgeDeg hodgeCohomologyCup)
open scoped TensorProduct CategoryTheory.Prod

universe u

namespace Stacks.HodgeWeil

attribute [local implicit_reducible] TopCat.Sheaf StacksDraft.KFlat.modulePullback
  StacksDraft.KFlat.modulePushforward CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.Tensor.ringSheaf

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] AlgebraicGeometry.SheafOfModules.abelianModules
  AlgebraicGeometry.SheafOfModules.hasSheafifyOpens
  AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijectiveOpens

/-! ### The cup product of Section 0FKU on complexes concentrated in degree zero -/

section General

/-- **The cup product followed by the canonical map to the total tensor complex is natural**,
on elements: `H(f)(x) ∪ H(g)(y) = H(Tot(f, g))(x ∪ y)`. -/
theorem totalCupPairing_naturality_apply {S : RingedSpace.{u, u}}
    {K K' M M' : CochainComplex (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} S.sheaf)) ℤ}
    (f : K ⟶ K') (g : M ⟶ M') (i j : ℤ) (x : cohomologyModule (DerivedCategory.Q.obj K) i)
    (y : cohomologyModule (DerivedCategory.Q.obj M) j) :
    (totalCupPairing K' M' i j).hom ((cohomologyMap f i).hom x ⊗ₜ (cohomologyMap g j).hom y) =
      (cohomologyMap (HomologicalComplex.mapBifunctorMap f g (sheafTensor S.sheaf) (up ℤ))
        (i + j)).hom ((totalCupPairing K M i j).hom (x ⊗ₜ y)) := by
  have hn : (Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
        S.sheaf)).map (DerivedCategory.Q.map f ×ₘ DerivedCategory.Q.map g) ≫
        (Stacks.Cohomology.DerivedPullbackTensor.derivedToTensorNatTrans S).app (K', M') =
      (Stacks.Cohomology.DerivedPullbackTensor.derivedToTensorNatTrans S).app (K, M) ≫
        DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap f g (sheafTensor S.sheaf)
          (up ℤ)) :=
    ((Stacks.Cohomology.DerivedPullbackTensor.derivedToTensorNatTrans S).naturality
      (X := (K, M)) (Y := (K', M')) (f ×ₘ g)).trans (congrArg (_ ≫ DerivedCategory.Q.map ·)
        (Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair_map _ f g))
  show ((DerivedCategory.homologyFunctor _ (i + j)).map ((baseSections S).map
      ((Stacks.Cohomology.DerivedPullbackTensor.derivedToTensorNatTrans S).app (K', M')))).hom
      ((Stacks.Cohomology.DerivedGlobalCupProduct.cupPairing
        (Stacks.Cohomology.DerivedGlobalCupProduct.cupProductOnSpace S) _ _ i j).hom
        (((DerivedCategory.homologyFunctor _ i).map ((baseSections S).map
          (DerivedCategory.Q.map f))).hom x ⊗ₜ
        ((DerivedCategory.homologyFunctor _ j).map ((baseSections S).map
          (DerivedCategory.Q.map g))).hom y)) =
    ((DerivedCategory.homologyFunctor _ (i + j)).map ((baseSections S).map
      (DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap f g (sheafTensor S.sheaf)
        (up ℤ))))).hom
      (((DerivedCategory.homologyFunctor _ (i + j)).map ((baseSections S).map
      ((Stacks.Cohomology.DerivedPullbackTensor.derivedToTensorNatTrans S).app (K, M)))).hom
      ((Stacks.Cohomology.DerivedGlobalCupProduct.cupPairing
        (Stacks.Cohomology.DerivedGlobalCupProduct.cupProductOnSpace S) _ _ i j).hom (x ⊗ₜ y)))
  rw [Stacks.Cohomology.DerivedGlobalCupProduct.cupPairing_naturality_apply]
  have e := congrArg (fun φ => ((DerivedCategory.homologyFunctor _ (i + j)).map
    ((baseSections S).map φ)).hom ((Stacks.Cohomology.DerivedGlobalCupProduct.cupPairing
      (Stacks.Cohomology.DerivedGlobalCupProduct.cupProductOnSpace S) _ _ i j).hom (x ⊗ₜ y))) hn
  exact (Stacks.Cohomology.HomologyPullback.map_map_comp_apply _ _ _ _ _).symm.trans
    (e.trans (Stacks.Cohomology.HomologyPullback.map_map_comp_apply _ _ _ _ _))

variable {X : RingedSpace.{u, u}} {A : TopCat.Sheaf CommRingCat.{u} X.carrier}

/-- A sheaf of `A`-modules as a `ℤ`-indexed complex concentrated in degree `0`. -/
abbrev singleInt
    (F : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)) :
    CochainComplex (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A))
      ℤ :=
  (HomologicalComplex.single _ (up ℤ) 0).obj F

/-- **The multiplication of `ℤ`-indexed complexes concentrated in degree `0` induced by a
morphism `F ⊗_A G ⟶ H`**: `Tot(F[0] ⊗_A G[0]) ⟶ H[0]`, the multiplication
`singleMultiplication` of the `ℕ`-indexed complexes read on their extensions by zero. -/
def singleIntMultiplication
    {F G H : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)}
    (m : ((sheafTensor.{u, u, u, u, u} A).obj F).obj G ⟶ H) :
    HomologicalComplex.mapBifunctor (singleInt F) (singleInt G) (sheafTensor.{u, u, u, u, u} A)
        (up ℤ) ⟶ singleInt H :=
  HomologicalComplex.mapBifunctorMap
      (HomologicalComplex.extendSingleIso embeddingUpNat F 0 0 embeddingUpNat_f_zero).inv
      (HomologicalComplex.extendSingleIso embeddingUpNat G 0 0 embeddingUpNat_f_zero).inv
      (sheafTensor.{u, u, u, u, u} A) (up ℤ) ≫
    multiplicationInt (singleMultiplication m) ≫
    (HomologicalComplex.extendSingleIso embeddingUpNat H 0 0 embeddingUpNat_f_zero).hom

/-- In degree `0`, on the summand `F ⊗_A G`, the multiplication of complexes concentrated in
degree `0` is the underlying morphism. -/
theorem ι_singleIntMultiplication_f
    {F G H : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)}
    (m : ((sheafTensor.{u, u, u, u, u} A).obj F).obj G ⟶ H) :
    HomologicalComplex.ιMapBifunctor (singleInt F) (singleInt G) (sheafTensor.{u, u, u, u, u} A)
        (up ℤ) 0 0 0 (add_zero 0) ≫ (singleIntMultiplication m).f 0 =
      ((sheafTensor.{u, u, u, u, u} A).map
          (HomologicalComplex.singleObjXSelf (up ℤ) 0 F).hom).app _ ≫
        ((sheafTensor.{u, u, u, u, u} A).obj F).map
          (HomologicalComplex.singleObjXSelf (up ℤ) 0 G).hom ≫ m ≫
        (HomologicalComplex.singleObjXSelf (up ℤ) 0 H).inv := by
  have key : ∀ {Z : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)}
      (z : ((HomologicalComplex.mapBifunctor (singleNat F) (singleNat G)
        (sheafTensor.{u, u, u, u, u} A) (up ℕ)).extend embeddingUpNat).X 0 ⟶ Z),
      HomologicalComplex.ιMapBifunctor ((singleNat F).extend embeddingUpNat)
        ((singleNat G).extend embeddingUpNat) (sheafTensor.{u, u, u, u, u} A) (up ℤ) 0 0 0
          (add_zero 0) ≫ (HomologicalComplex.mapBifunctorExtendHom
            (sheafTensor.{u, u, u, u, u} A) (singleNat F) (singleNat G)).f 0 ≫ z =
        ((sheafTensor.{u, u, u, u, u} A).map ((singleNat F).extendXIso embeddingUpNat
            (i' := 0) (i := 0) rfl).hom).app _ ≫
          ((sheafTensor.{u, u, u, u, u} A).obj ((singleNat F).X 0)).map
            ((singleNat G).extendXIso embeddingUpNat (i' := 0) (i := 0) rfl).hom ≫
          HomologicalComplex.ιMapBifunctor (singleNat F) (singleNat G)
            (sheafTensor.{u, u, u, u, u} A) (up ℕ) 0 0 0 rfl ≫
          ((HomologicalComplex.mapBifunctor (singleNat F) (singleNat G)
            (sheafTensor.{u, u, u, u, u} A) (up ℕ)).extendXIso embeddingUpNat (i' := 0) (i := 0)
              rfl).inv ≫ z :=
    fun z => HomologicalComplex.ι_mapBifunctorExtendHom_f_assoc (sheafTensor.{u, u, u, u, u} A)
      (singleNat F) (singleNat G) 0 0 0 (add_zero _) z
  let m' : HomologicalComplex.mapBifunctor (singleNat F) (singleNat G)
      (sheafTensor.{u, u, u, u, u} A) (up ℕ) ⟶ singleNat H := singleMultiplication m
  have hm' : m'.f 0 = AlgebraicGeometry.SheafOfModules.singleMultiplicationX m ≫
      (HomologicalComplex.singleObjXSelf (up ℕ) 0 H).inv :=
    HomologicalComplex.mkHomToSingle_f _ _
  show HomologicalComplex.ιMapBifunctor (singleInt F) (singleInt G)
      (sheafTensor.{u, u, u, u, u} A) (up ℤ) 0 0 0 (add_zero 0) ≫
      (HomologicalComplex.mapBifunctorMap
        (HomologicalComplex.extendSingleIso embeddingUpNat F 0 0 embeddingUpNat_f_zero).inv
        (HomologicalComplex.extendSingleIso embeddingUpNat G 0 0 embeddingUpNat_f_zero).inv
        (sheafTensor.{u, u, u, u, u} A) (up ℤ) ≫
      (HomologicalComplex.mapBifunctorExtendHom (sheafTensor.{u, u, u, u, u} A) (singleNat F)
        (singleNat G) ≫ HomologicalComplex.extendMap m' embeddingUpNat) ≫
      (HomologicalComplex.extendSingleIso embeddingUpNat H 0 0 embeddingUpNat_f_zero).hom).f 0 = _
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    HomologicalComplex.ι_mapBifunctorMap_assoc, Category.assoc, key,
    HomologicalComplex.extendMap_f m' embeddingUpNat (i := 0) (i' := 0) rfl, hm',
    AlgebraicGeometry.SheafOfModules.singleMultiplicationX]
  simp only [Category.assoc, Iso.inv_hom_id_assoc,
    HomologicalComplex.extendSingleIso_hom_f, HomologicalComplex.extendSingleIso_inv_f,
    HomologicalComplex.ι_mapBifunctorDesc_assoc]
  simp only [HomologicalComplex.singleObjXSelf, Functor.map_comp, NatTrans.comp_app,
    Category.assoc, NatTrans.naturality_assoc, Iso.map_inv_hom_id_app_assoc,
    Iso.map_inv_hom_id_assoc]

/-- On the class of a local pure tensor of the summand `F ⊗_A G` in degree `0`, the
multiplication of complexes concentrated in degree `0` is the underlying morphism. -/
theorem singleIntMultiplication_val_app
    {F G H : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)}
    (m : ((sheafTensor.{u, u, u, u, u} A).obj F).obj G ⟶ H) (U : (Opens X.carrier)ᵒᵖ)
    (x : ((singleInt F).X 0).val.obj U) (y : ((singleInt G).X 0).val.obj U) :
    (HomologicalComplex.ιMapBifunctor (singleInt F) (singleInt G) (sheafTensor.{u, u, u, u, u} A)
        (up ℤ) 0 0 0 (add_zero 0) ≫ (singleIntMultiplication m).f 0).val.app U
        (((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.SheafOfModules.Tensor.ringSheaf A)
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf A).obj)).unit.app
          (PresheafOfModules.tensorObj ((singleInt F).X 0).val ((singleInt G).X 0).val)).app U
            (x ⊗ₜ[A.obj.obj U] y)) =
      (HomologicalComplex.singleObjXSelf (up ℤ) 0 H).inv.val.app U
        (m.val.app U (((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.SheafOfModules.Tensor.ringSheaf A)
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf A).obj)).unit.app
          (PresheafOfModules.tensorObj F.val G.val)).app U
            ((HomologicalComplex.singleObjXSelf (up ℤ) 0 F).hom.val.app U x ⊗ₜ[A.obj.obj U]
              (HomologicalComplex.singleObjXSelf (up ℤ) 0 G).hom.val.app U y))) := by
  rw [ι_singleIntMultiplication_f]
  refine congrArg (fun t => (HomologicalComplex.singleObjXSelf (up ℤ) 0 H).inv.val.app U
    (m.val.app U t)) ?_
  refine (congrArg (fun t => ((((sheafTensor.{u, u, u, u, u} A).obj F).map
      (HomologicalComplex.singleObjXSelf (up ℤ) 0 G).hom).val.app U) t)
    (Stacks.SheafOfModules.FlatSquareZero.tensorRight_map_tmul A ((singleInt G).X 0)
      (HomologicalComplex.singleObjXSelf (up ℤ) 0 F).hom U x y)).trans ?_
  exact Stacks.SheafOfModules.FlatSquareZero.tensorLeft_map_tmul A F
    (HomologicalComplex.singleObjXSelf (up ℤ) 0 G).hom U _ y

variable {φ : A ⟶ X.sheaf}
  (B : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) (moduleOfDifferentials.{u, u, u} φ))

/-- **The cup product along a multiplication of forms, through the `ℤ`-indexed complexes
concentrated in degree `0`**: the cup product of Section 0FKU followed by the canonical map to
the total tensor complex and the multiplication `singleIntMultiplication m`. -/
theorem hodgeComponentCup_eq_totalCupPairing {p p' r : ℕ} (m : FormsMultiplication B p p' r)
    (q q' : ℤ) (ξ : hodgeCohomologyComponent B p q) (ζ : hodgeCohomologyComponent B p' q') :
    hodgeComponentCup B m q q' ξ ζ =
      (cohomologyMap (S := baseRingedSpace A) (singleIntMultiplication m) (q + q')).hom
        ((totalCupPairing (S := baseRingedSpace A) (singleInt (A := A) (deRhamTerm B p))
          (singleInt (A := A) (deRhamTerm B p')) q q').hom
          (toHodgeComponentBase B ξ ⊗ₜ toHodgeComponentBase B ζ)) := by
  have e := totalCupPairing_naturality_apply (S := baseRingedSpace A)
    (HomologicalComplex.extendSingleIso embeddingUpNat (deRhamTerm B p) 0 0
      embeddingUpNat_f_zero).inv
    (HomologicalComplex.extendSingleIso embeddingUpNat (deRhamTerm B p') 0 0
      embeddingUpNat_f_zero).inv q q'
    (toHodgeComponentBase B ξ) (toHodgeComponentBase B ζ)
  rw [hodgeComponentCup, AlgebraicGeometry.SheafOfModules.canonicalPairingModule_eq]
  refine (congrArg (fun t => (cohomologyMap (S := baseRingedSpace A)
    (HomologicalComplex.extendSingleIso embeddingUpNat (deRhamTerm B r) 0 0
      embeddingUpNat_f_zero).hom (q + q')).hom
    ((AlgebraicGeometry.SheafOfModules.cohomologyModuleMap (q + q')
      (multiplicationInt (singleMultiplication m))).hom t)) e).trans ?_
  simp only [singleIntMultiplication, cohomologyMap, Functor.map_comp, ModuleCat.hom_comp]
  rfl

/-- The global cocycle `1` of `Γ(X, Ω^0[0])`: the image of the global section `1` of the
structure sheaf under the chain map `𝒪[0] ⟶ Ω^0[0]` of the global function `1`. -/
def formsOneCycle :
    (Stacks.Cohomology.DerivedGlobalCupProduct.sectionsComplex (baseRingedSpace A)
      (singleInt (X := X) (A := A) (@deRhamTerm X A φ B 0))).cycles 0 :=
  (HomologicalComplex.cyclesMap
    (((Stacks.Cohomology.DerivedGlobalCupProduct.globalSections
        (baseRingedSpace A)).mapHomologicalComplex
      (up ℤ)).map (HomologicalComplex.extendSingleIso embeddingUpNat (@deRhamTerm X A φ B 0) 0 0
        embeddingUpNat_f_zero).hom) 0).hom
    ((HomologicalComplex.cyclesMap
      (((Stacks.Cohomology.DerivedGlobalCupProduct.globalSections
          (baseRingedSpace A)).mapHomologicalComplex
        (up ℤ)).map (Stacks.DeRham.GysinCupHodge.unitComplexSectionMap (X := baseRingedSpace A)
          (@deRhamTerm X A φ B 0) (formsOne B))) 0).hom
      ((Stacks.Cohomology.DerivedGlobalCupProduct.unitCycleHom (baseRingedSpace A)).hom 1))

/-- **The unit class is the class of the global cocycle `1`** of `Γ(X, Ω^0[0])`. -/
theorem hodgeOne_eq_globalClass :
    hodgeOne B = Stacks.Cohomology.DerivedGlobalCupProduct.globalClass (X := baseRingedSpace A)
      (singleInt (X := X) (A := A) (@deRhamTerm X A φ B 0)) 0 (formsOneCycle B) :=
  (congrArg (fun t => ((DerivedCategory.homologyFunctor _ 0).map
    ((baseSections (baseRingedSpace A)).map (DerivedCategory.Q.map
      (HomologicalComplex.extendSingleIso embeddingUpNat (@deRhamTerm X A φ B 0) 0 0
        embeddingUpNat_f_zero).hom))).hom t)
    (Stacks.Cohomology.DerivedGlobalCupProduct.globalClass_map (baseRingedSpace A)
      (Stacks.DeRham.GysinCupHodge.unitComplexSectionMap (X := baseRingedSpace A)
        (@deRhamTerm X A φ B 0) (formsOne B)) 0 _)).trans
    (Stacks.Cohomology.DerivedGlobalCupProduct.globalClass_map (baseRingedSpace A) _ 0 _)

/-- The global section underlying the global cocycle `1` of `Γ(X, Ω^0[0])` is the global
function `1`. -/
theorem iCycles_formsOneCycle :
    ((Stacks.Cohomology.DerivedGlobalCupProduct.sectionsComplex (baseRingedSpace A)
      (singleInt (X := X) (A := A) (@deRhamTerm X A φ B 0))).iCycles 0).hom (formsOneCycle B) =
      (HomologicalComplex.singleObjXSelf (up ℤ) 0 (@deRhamTerm X A φ B 0)).inv.val.app (op ⊤)
        ((formsOne B).val (op ⊤)) := by
  let Γc := (Stacks.Cohomology.DerivedGlobalCupProduct.globalSections
    (baseRingedSpace A)).mapHomologicalComplex (up ℤ)
  let u := (@deRhamTerm X A φ B 0).unitHomEquiv.symm (formsOne B)
  have hm : Stacks.DeRham.GysinCupHodge.unitComplexSectionMap (X := baseRingedSpace A)
      (@deRhamTerm X A φ B 0) (formsOne B) ≫ (HomologicalComplex.extendSingleIso embeddingUpNat
        (@deRhamTerm X A φ B 0) 0 0 embeddingUpNat_f_zero).hom =
      (HomologicalComplex.single _ (up ℤ) 0).map u :=
    (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (Iso.inv_hom_id _)).trans
      (Category.comp_id _))
  have hz : ((Stacks.Cohomology.DerivedGlobalCupProduct.sectionsComplex (baseRingedSpace A)
      (Stacks.Cohomology.DerivedGlobalCupProduct.unitComplexR (baseRingedSpace A))).iCycles 0).hom
        ((Stacks.Cohomology.DerivedGlobalCupProduct.unitCycleHom (baseRingedSpace A)).hom 1) =
      Stacks.Cohomology.DerivedGlobalCupProduct.unitSection (baseRingedSpace A) 0 :=
    (congrArg (fun t => ((Stacks.Cohomology.DerivedGlobalCupProduct.sectionsComplex
      (baseRingedSpace A) (Stacks.Cohomology.DerivedGlobalCupProduct.unitComplexR
        (baseRingedSpace A))).iCycles 0).hom t)
      (one_smul (baseRing (baseRingedSpace A))
        (Stacks.Cohomology.DerivedGlobalCupProduct.unitCycle (baseRingedSpace A) 0))).trans
      (Stacks.Cohomology.DerivedGlobalCupProduct.iCycles_unitCycle _ 0)
  have c1 := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i
    (Γc.map (HomologicalComplex.extendSingleIso embeddingUpNat (@deRhamTerm X A φ B 0) 0 0
      embeddingUpNat_f_zero).hom) 0)
    ((HomologicalComplex.cyclesMap (Γc.map (Stacks.DeRham.GysinCupHodge.unitComplexSectionMap
      (X := baseRingedSpace A) (@deRhamTerm X A φ B 0) (formsOne B))) 0).hom
      ((Stacks.Cohomology.DerivedGlobalCupProduct.unitCycleHom (baseRingedSpace A)).hom 1))
  have c2 := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i
    (Γc.map (Stacks.DeRham.GysinCupHodge.unitComplexSectionMap
      (X := baseRingedSpace A) (@deRhamTerm X A φ B 0) (formsOne B))) 0)
    ((Stacks.Cohomology.DerivedGlobalCupProduct.unitCycleHom (baseRingedSpace A)).hom 1)
  refine c1.trans ((congrArg (fun t => ConcreteCategory.hom
    ((Γc.map (HomologicalComplex.extendSingleIso embeddingUpNat (@deRhamTerm X A φ B 0) 0 0
      embeddingUpNat_f_zero).hom).f 0) t) c2).trans ?_)
  refine (congrArg (fun t => ConcreteCategory.hom
    ((Γc.map (HomologicalComplex.extendSingleIso embeddingUpNat (@deRhamTerm X A φ B 0) 0 0
      embeddingUpNat_f_zero).hom).f 0) (ConcreteCategory.hom
        ((Γc.map (Stacks.DeRham.GysinCupHodge.unitComplexSectionMap (X := baseRingedSpace A)
          (@deRhamTerm X A φ B 0) (formsOne B))).f 0) t)) hz).trans ?_
  have hv := congrArg (fun t => (t.f 0).val.app (op ⊤)
    (Stacks.Cohomology.DerivedGlobalCupProduct.unitSection (baseRingedSpace A) 0)) hm
  refine hv.trans ?_
  rw [HomologicalComplex.single_map_f_self]
  exact congrArg (fun z => (HomologicalComplex.singleObjXSelf (up ℤ) 0
      (@deRhamTerm X A φ B 0)).inv.val.app (op ⊤) z)
    ((congrArg (fun z => u.val.app (op ⊤) z) (Stacks.SheafOfModules.hom_val_app_inv_val_app
      (HomologicalComplex.singleObjXSelf (up ℤ) 0
        (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)))
      (op ⊤) (1 : (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A).obj.obj (op ⊤)))).trans
      (congrArg (fun s => s.val (op ⊤))
        ((@deRhamTerm X A φ B 0).unitHomEquiv.apply_symm_apply (formsOne B))))

end General

/-! ### The canonical map of forms is multiplicative -/

section Hodge

open RingedSpaceModuleAdjunction Stacks.DeRhamDirectImage Stacks.DeRhamBaseChange
open Stacks.Cohomology.NaiveCupProductOnRingedSpaces (naiveCupProduct pushforwardComplex)
open Stacks.Cohomology.CupProductAndDerivedPushforwardOnRingedSpaces (pushforwardComparisonQ
  pushforwardComparisonQ_naturality naiveCupProduct_relativeCupProduct)
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPushforward)
open Stacks.Cohomology.DerivedRelativeCupProduct (relativeCupProduct)
open Stacks.Cohomology.DerivedPullbackTensor (derivedToTensorNatTrans totalComplexPair)
open Stacks.Cohomology.LerayCupPairing (lerayCohomologyIso)

/-- The tensor product of sheaves of modules preserves zero morphisms, being additive. -/
local instance preservesZeroMorphisms_sheafTensor_ringedSpace (Y : RingedSpace.{u, u}) :
    (sheafTensor.{u, u, u, u, u} Y.sheaf).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_additive _

/-- Tensoring with a fixed sheaf of modules preserves zero morphisms, being additive. -/
local instance preservesZeroMorphisms_sheafTensor_obj_ringedSpace (Y : RingedSpace.{u, u})
    (M : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Y.sheaf)) :
    ((sheafTensor.{u, u, u, u, u} Y.sheaf).obj M).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_additive _

variable {X X' S S' : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
  (w : g' ≫ f = f' ≫ g)

/-- The morphism of ringed spaces `(X', f'⁻¹𝒪_{S'}) ⟶ (X, f⁻¹𝒪_S)` of the square. -/
local notation "g₀" => inverseImageBaseMap g' f' f g w

/-- The tensor, exterior and symmetric algebras of the sheaf of relative differentials of
`f : X ⟶ S`, which are `Scheme.Hom.deRhamAlgebras f`, typed through the structure map
`f⁻¹𝒪_S ⟶ 𝒪_X`, the form in which the Hodge cohomology groups and their cup product are
stated. -/
abbrev formsAlgebras {X S : Scheme.{u}} (f : X ⟶ S) :
    _root_.SheafOfModules.TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology X.carrier)
      (moduleOfDifferentials.{u, u, u} (AlgebraicGeometry.inverseImageStructureMap f)) :=
  AlgebraicGeometry.SheafOfModules.differentialAlgebras
    (AlgebraicGeometry.inverseImageStructureMap f)

/-- `Ω^p_{X/S}[0]`, at the spelling of the category of modules over `(X, f⁻¹𝒪_S)` at which the
tensor product of sheaves of modules is stated. -/
abbrev formsSingleModules (f : X ⟶ S) (p : ℕ) :
    CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules
      (inverseImageBase f)) ℤ :=
  formsSingle f p

/-- The canonical map `Ω^p_{X/S}[0] ⟶ g₀_*(Ω^p_{X'/S'}[0])`, at the spelling of
`formsSingleModules`. -/
abbrev formsSinglePushforwardModules (p : ℕ) :
    formsSingleModules f p ⟶
      (pushforwardComplex g₀).obj (formsSingleModules f' p) :=
  formsSinglePushforward g' f' f g w p

/-- **The wedge product `Tot(Ω^p_{X/S}[0] ⊗ Ω^{p'}_{X/S}[0]) ⟶ Ω^{p + p'}_{X/S}[0]`** of
complexes of `f⁻¹𝒪_S`-modules concentrated in degree `0`. -/
abbrev formsSingleWedge (f : X ⟶ S) (p p' : ℕ) :
    (totalComplexPair (sheafTensor.{u, u, u, u, u} (inverseImageBase f).sheaf)).obj
        (formsSingleModules f p, formsSingleModules f p') ⟶
      formsSingleModules f (p + p') :=
  singleIntMultiplication
    (AlgebraicGeometry.SheafOfModules.exteriorProductComponent (Scheme.Hom.deRhamAlgebras f) p p')

/-- On a local pure tensor in degree `0`, the wedge product of complexes concentrated in degree
`0` is the wedge product of forms. -/
theorem formsSingleWedge_val_app (f : X ⟶ S) (p p' : ℕ) (U : (Opens X.carrier)ᵒᵖ)
    (x : ((formsSingleModules f p).X 0).val.obj U) (y : ((formsSingleModules f p').X 0).val.obj U) :
    (HomologicalComplex.ιMapBifunctor (formsSingleModules f p) (formsSingleModules f p')
        (sheafTensor.{u, u, u, u, u} (inverseImageBase f).sheaf) (up ℤ) 0 0 0 (add_zero 0) ≫
        (formsSingleWedge f p p').f 0).val.app U
        (((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.SheafOfModules.Tensor.ringSheaf (inverseImageBase f).sheaf)
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (inverseImageBase f).sheaf).obj)).unit.app
          (PresheafOfModules.tensorObj ((formsSingleModules f p).X 0).val
            ((formsSingleModules f p').X 0).val)).app U
            (x ⊗ₜ[(inverseImageBase f).sheaf.obj.obj U] y)) =
      (HomologicalComplex.singleObjXSelf (up ℤ) 0
          ((Scheme.Hom.deRhamComplex f).X (p + p'))).inv.val.app U
        (AlgebraicGeometry.SheafOfModules.formProduct (Scheme.Hom.deRhamAlgebras f) p p' U
          ((HomologicalComplex.singleObjXSelf (up ℤ) 0
            ((Scheme.Hom.deRhamComplex f).X p)).hom.val.app U x)
          ((HomologicalComplex.singleObjXSelf (up ℤ) 0
            ((Scheme.Hom.deRhamComplex f).X p')).hom.val.app U y)) :=
  (singleIntMultiplication_val_app _ U x y).trans (congrArg _
    (AlgebraicGeometry.SheafOfModules.exteriorProductComponent_unit_apply _ p p' U _ _))

/-- The class of a local pure tensor `x ⊗ y` in the tensor product of two sheaves of modules
over a ringed space. -/
abbrev tensorSectionClass (Z : RingedSpace.{u, u})
    {F G : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z}
    (U : (Opens Z.carrier)ᵒᵖ) (x : F.val.obj U) (y : G.val.obj U) :
    (((sheafTensor.{u, u, u, u, u} Z.sheaf).obj F).obj G).val.obj U :=
  ((PresheafOfModules.sheafificationAdjunction
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf Z.sheaf).obj)).unit.app
      (F.val.tensorObj G.val)).app U (x ⊗ₜ[Z.sheaf.obj.obj U] y)

/-- The total tensor complex of two canonical maps of forms, on a local pure tensor in degree
`0`. -/
theorem ι_mapBifunctorMap_formsSinglePushforward_val_app (p p' : ℕ) (U : (Opens X.carrier)ᵒᵖ)
    (x : ((formsSingleModules f p).X 0).val.obj U) (y : ((formsSingleModules f p').X 0).val.obj U)
    (hab : (up ℤ).π (up ℤ) (up ℤ) (0, 0) = 0) :
    (HomologicalComplex.ιMapBifunctor (formsSingleModules f p) (formsSingleModules f p')
        (sheafTensor.{u, u, u, u, u} (inverseImageBase f).sheaf)
        (up ℤ) 0 0 0 hab ≫
      (HomologicalComplex.mapBifunctorMap (formsSinglePushforwardModules g' f' f g w p)
          (formsSinglePushforwardModules g' f' f g w p') (sheafTensor.{u, u, u, u, u}
          (inverseImageBase f).sheaf) (up ℤ)).f 0).val.app U
        (tensorSectionClass (inverseImageBase f) U x y) =
      (HomologicalComplex.ιMapBifunctor ((pushforwardComplex g₀).obj (formsSingleModules f' p))
          ((pushforwardComplex g₀).obj (formsSingleModules f' p'))
          (sheafTensor.{u, u, u, u, u} (inverseImageBase f).sheaf) (up ℤ) 0 0 0 hab).val.app U
        (tensorSectionClass (inverseImageBase f) U
          (((formsSinglePushforwardModules g' f' f g w p).f 0).val.app U x)
          (((formsSinglePushforwardModules g' f' f g w p').f 0).val.app U y)) :=
  (congrArg (fun t => t.val.app U (tensorSectionClass (inverseImageBase f) U x y))
    (HomologicalComplex.ι_mapBifunctorMap (formsSinglePushforwardModules g' f' f g w p)
        (formsSinglePushforwardModules g' f' f g w p') (sheafTensor.{u, u, u, u, u}
        (inverseImageBase f).sheaf) (up ℤ) 0 0 0 hab)).trans
    (congrArg (fun t => (HomologicalComplex.ιMapBifunctor ((pushforwardComplex g₀).obj
        (formsSingleModules f' p)) ((pushforwardComplex g₀).obj (formsSingleModules f' p'))
        (sheafTensor.{u, u, u, u, u} (inverseImageBase f).sheaf) (up ℤ) 0 0 0 hab).val.app U t)
      (Stacks.RingedSpace.tensorSheaf_map_unit_tmul (inverseImageBase f)
          ((formsSinglePushforwardModules g' f' f g w p).f 0)
        ((formsSinglePushforwardModules g' f' f g w p').f 0) U x y))

/-- The naive cup product followed by the direct image of the wedge product on `X'`, on a local
pure tensor in degree `0`: it is the wedge product of the two forms on `X'`. -/
theorem ι_naiveCupProduct_formsSingleWedge_val_app (p p' : ℕ) (U : (Opens X.carrier)ᵒᵖ)
    (u : (((pushforwardComplex g₀).obj (formsSingleModules f' p)).X 0).val.obj U)
    (v : (((pushforwardComplex g₀).obj (formsSingleModules f' p')).X 0).val.obj U)
    (hab : (up ℤ).π (up ℤ) (up ℤ) (0, 0) = 0) :
    (HomologicalComplex.ιMapBifunctor ((pushforwardComplex g₀).obj (formsSingleModules f' p))
        ((pushforwardComplex g₀).obj (formsSingleModules f' p'))
        (sheafTensor.{u, u, u, u, u} (inverseImageBase f).sheaf) (up ℤ) 0 0 0 hab ≫
        (naiveCupProduct g₀ (formsSingleModules f' p) (formsSingleModules f' p')).f 0 ≫
        ((pushforwardComplex g₀).map (formsSingleWedge f' p p')).f 0).val.app U
        (tensorSectionClass (inverseImageBase f) U u v) =
      (HomologicalComplex.singleObjXSelf (up ℤ) 0
          ((Scheme.Hom.deRhamComplex f').X (p + p'))).inv.val.app ((Opens.map g'.base).op.obj U)
        (AlgebraicGeometry.SheafOfModules.formProduct (Scheme.Hom.deRhamAlgebras f') p p'
          ((Opens.map g'.base).op.obj U)
          ((HomologicalComplex.singleObjXSelf (up ℤ) 0
            ((Scheme.Hom.deRhamComplex f').X p)).hom.val.app _ u)
          ((HomologicalComplex.singleObjXSelf (up ℤ) 0
            ((Scheme.Hom.deRhamComplex f').X p')).hom.val.app _ v)) := by
  have r2 := congrArg (fun t =>
      (((pushforwardComplex g₀).map (formsSingleWedge f' p p')).f 0).val.app U
        (t.val.app U (tensorSectionClass (inverseImageBase f) U u v)))
    (Stacks.Cohomology.NaiveCupProductSummand.ι_naiveCupProduct g₀
      (formsSingleModules f' p) (formsSingleModules f' p') 0 0 0 hab)
  refine r2.trans ?_
  have r3 := Stacks.RingedSpace.pushforwardTensorMap_unit_tmul g₀
    ((formsSingleModules f' p).X 0) ((formsSingleModules f' p').X 0) U u v
  refine (congrArg (fun t =>
      (((pushforwardComplex g₀).map (formsSingleWedge f' p p')).f 0).val.app U
        (((StacksDraft.KFlat.modulePushforward g₀).map
        (HomologicalComplex.ιMapBifunctor (formsSingleModules f' p) (formsSingleModules f' p')
          (sheafTensor.{u, u, u, u, u} (inverseImageBase f').sheaf) (up ℤ) 0 0 0 hab)).val.app U
            t)) r3).trans ?_
  exact formsSingleWedge_val_app f' p p' ((Opens.map g'.base).op.obj U) u v

/-- **The canonical map of forms is multiplicative**, as a morphism of complexes: the square

`Tot(Ω^p_{X/S}[0] ⊗ Ω^{p'}_{X/S}[0]) --∧--> Ω^{p+p'}_{X/S}[0]`,
`Tot(g₀_*Ω^p_{X'/S'}[0] ⊗ g₀_*Ω^{p'}_{X'/S'}[0]) ⟶ g₀_*Tot(Ω^p_{X'/S'}[0] ⊗ Ω^{p'}_{X'/S'}[0])
--g₀_*∧--> g₀_*Ω^{p+p'}_{X'/S'}[0]`

commutes, the vertical maps being the canonical maps of forms and the bottom-left map the naive
cup product of Tag 0FP3. On local pure tensors it is the multiplicativity of the pullback of
differential forms. -/
theorem formsSingleWedge_comp_formsSinglePushforward (p p' : ℕ) :
    formsSingleWedge f p p' ≫ formsSinglePushforwardModules g' f' f g w (p + p') =
      (totalComplexPair (sheafTensor.{u, u, u, u, u} (inverseImageBase f).sheaf)).map
          (formsSinglePushforwardModules g' f' f g w p ×ₘ
            formsSinglePushforwardModules g' f' f g w p') ≫
        naiveCupProduct g₀ (formsSingleModules f' p) (formsSingleModules f' p') ≫
        (pushforwardComplex g₀).map (formsSingleWedge f' p p') := by
  refine HomologicalComplex.hom_ext _ _ fun n =>
    HomologicalComplex.mapBifunctor.hom_ext fun a b hab => ?_
  by_cases h0 : a = 0 ∧ b = 0
  · obtain ⟨rfl, rfl⟩ := h0
    obtain rfl : (0 : ℤ) = n := (add_zero (0 : ℤ)).symm.trans hab
    rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, HomologicalComplex.comp_f,
      Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair_map]
    dsimp only
    refine AlgebraicGeometry.SheafOfModules.sheafTensor_hom_ext (X := inverseImageBase f)
      (A := (inverseImageBase f).sheaf) fun U x y => ?_
    refine (congrArg (fun t => ((formsSinglePushforwardModules g' f' f g w (p + p')).f 0).val.app
      U t) (formsSingleWedge_val_app f p p' U x y)).trans ?_
    refine (formsSinglePushforward_f_zero_val_app g' f' f g w (p + p') U _).trans ?_
    refine (Scheme.Hom.relativeDifferentialFormsPullback_mul g' f f' g w p p' U.unop x y).trans ?_
    refine Eq.trans ?_ (congrArg (fun t => ((naiveCupProduct g₀ (formsSingleModules f' p)
        (formsSingleModules f' p')).f 0 ≫ ((pushforwardComplex g₀).map
          (formsSingleWedge f' p p')).f 0).val.app U t)
      (ι_mapBifunctorMap_formsSinglePushforward_val_app g' f' f g w p p' U x y hab)).symm
    refine Eq.trans ?_ (ι_naiveCupProduct_formsSingleWedge_val_app g' f' f g w p p' U _ _ hab).symm
    rw [formsSinglePushforward_f_zero_val_app, formsSinglePushforward_f_zero_val_app]
    rfl
  · have hz : IsZero (((sheafTensor.{u, u, u, u, u} (inverseImageBase f).sheaf).obj
        ((formsSingleModules f p).X a)).obj ((formsSingleModules f p').X b)) := by
      by_cases ha : a = 0
      · exact AlgebraicGeometry.SheafOfModules.isZero_tensorFunctor_obj_obj_of_right _
          (HomologicalComplex.isZero_single_obj_X (up ℤ) 0 _ b (by omega))
      · exact AlgebraicGeometry.SheafOfModules.isZero_tensorFunctor_obj_obj_of_left
          (HomologicalComplex.isZero_single_obj_X (up ℤ) 0 _ a ha) _
    exact hz.eq_of_src _ _

/-- **The canonical map `Ω^p_{X/S}[0] ⟶ Rg₀_*Ω^p_{X'/S'}[0]`** in `D(X, f⁻¹𝒪_S)`: the canonical
map of forms followed by the comparison `g₀_* ⟶ Rg₀_*`. It induces the pullback on Hodge
cohomology. -/
abbrev formsComparisonQ (p : ℕ) :
    DerivedCategory.Q.obj (formsSingleModules f p) ⟶
      (derivedPushforward g₀).obj
        (DerivedCategory.Q.obj (formsSingleModules f' p)) :=
  DerivedCategory.Q.map (formsSinglePushforwardModules g' f' f g w p) ≫
    pushforwardComparisonQ g₀ (formsSingleModules f' p)

/-- **The canonical map `Ω^p_{X/S}[0] ⟶ Rg₀_*Ω^p_{X'/S'}[0]` is multiplicative** in the derived
category: it carries the multiplication `Ω^p[0] ⊗^𝐋 Ω^{p'}[0] ⟶ Tot(Ω^p[0] ⊗ Ω^{p'}[0]) --∧-->
Ω^{p+p'}[0]` to the relative cup product of Tag 0B68 followed by `Rg₀_*` of the multiplication
on `X'`. This is `formsSingleWedge_comp_formsSinglePushforward` combined with Tag 0FP3. -/
theorem formsComparisonQ_multiplicative (p p' : ℕ) :
    (derivedToTensorNatTrans (inverseImageBase f)).app
        (formsSingleModules f p, formsSingleModules f p') ≫
        DerivedCategory.Q.map (formsSingleWedge f p p') ≫ formsComparisonQ g' f' f g w (p + p') =
      (Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
          (inverseImageBase f).sheaf)).map
          (formsComparisonQ g' f' f g w p ×ₘ formsComparisonQ g' f' f g w p') ≫
        relativeCupProduct g₀
          (DerivedCategory.Q.obj (formsSingleModules f' p)) (DerivedCategory.Q.obj
              (formsSingleModules f' p')) ≫
        (derivedPushforward g₀).map
          ((derivedToTensorNatTrans (inverseImageBase f')).app
              (formsSingleModules f' p, formsSingleModules f' p') ≫
            DerivedCategory.Q.map (formsSingleWedge f' p p')) := by
  have h0 := naiveCupProduct_relativeCupProduct g₀
    (formsSingleModules f' p) (formsSingleModules f' p')
  have h1 := pushforwardComparisonQ_naturality g₀
    (formsSingleWedge f' p p')
  have h2 := (derivedToTensorNatTrans (inverseImageBase f)).naturality
    (formsSinglePushforwardModules g' f' f g w p ×ₘ formsSinglePushforwardModules g' f' f g w p')
  have hM := congrArg DerivedCategory.Q.map
    (formsSingleWedge_comp_formsSinglePushforward g' f' f g w p p')
  rw [Functor.map_comp, Functor.map_comp, Functor.map_comp] at hM
  simp only [Functor.comp_map, Functor.prod_map] at h2
  simp only [formsComparisonQ]
  rw [reassoc_of% hM, h1, ← reassoc_of% h2, reassoc_of% h0]
  simp only [Functor.map_comp]
  rw [← Functor.map_comp_assoc]
  rfl

/-- **The cup product along the wedge product is compatible with pullback**:
`g'^*(ξ ∪ ζ) = g'^*ξ ∪ g'^*ζ` for `ξ ∈ H^q(X, Ω^p_{X/S})` and `ζ ∈ H^{q'}(X, Ω^{p'}_{X/S})`,
for the cup product of Section 0FKU along the wedge product of Tag 0FM2. -/
theorem hodgePullback_hodgeComponentCup (p p' : ℕ) (q q' : ℤ)
    (ξ : hodgeCohomologyComponent (formsAlgebras f) p q)
    (ζ : hodgeCohomologyComponent (formsAlgebras f) p' q') :
    hodgePullback g' f' f g w (p + p') (q + q')
        (hodgeComponentCup (formsAlgebras f)
          (AlgebraicGeometry.SheafOfModules.exteriorProductComponent
            (formsAlgebras f) p p') q q' ξ ζ) =
      hodgeComponentCup (formsAlgebras f')
        (AlgebraicGeometry.SheafOfModules.exteriorProductComponent
          (formsAlgebras f') p p') q q'
        (hodgePullback g' f' f g w p q ξ) (hodgePullback g' f' f g w p' q' ζ) := by
  refine (congrArg (fun t => hodgePullback g' f' f g w (p + p') (q + q') t)
    (hodgeComponentCup_eq_totalCupPairing (formsAlgebras f) _ q q' ξ ζ)).trans ?_
  refine Eq.trans ?_ (hodgeComponentCup_eq_totalCupPairing (formsAlgebras f') _ q q'
    (hodgePullback g' f' f g w p q ξ) (hodgePullback g' f' f g w p' q' ζ)).symm
  have e1 : (lerayCohomologyIso g₀ (DerivedCategory.Q.obj (formsSingleModules f' (p + p')))
      (q + q')).hom
      (((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing (inverseImageBase f)))
          (q + q')).map ((baseSections (inverseImageBase f)).map
          (((derivedToTensorNatTrans (inverseImageBase f)).app
          (formsSingleModules f p, formsSingleModules f p')) ≫
          (DerivedCategory.Q.map (formsSingleWedge f p p')) ≫ formsComparisonQ g' f' f g w
          (p + p')))).hom
        ((Stacks.Cohomology.DerivedGlobalCupProduct.cupPairing
          (Stacks.Cohomology.DerivedGlobalCupProduct.cupProductOnSpace (inverseImageBase f))
          (DerivedCategory.Q.obj (formsSingleModules f p))
          (DerivedCategory.Q.obj (formsSingleModules f p')) q q').hom (ξ ⊗ₜ ζ))) =
      (lerayCohomologyIso g₀ (DerivedCategory.Q.obj (formsSingleModules f' (p + p'))) (q + q')).hom
      (((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing (inverseImageBase f)))
          (q + q')).map ((baseSections (inverseImageBase f)).map
          (formsComparisonQ g' f' f g w (p + p')))).hom
        (((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing (inverseImageBase f)))
            (q + q')).map ((baseSections (inverseImageBase f)).map
            (DerivedCategory.Q.map (formsSingleWedge f p p')))).hom
            (((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing (inverseImageBase f)))
            (q + q')).map ((baseSections (inverseImageBase f)).map
            ((derivedToTensorNatTrans (inverseImageBase f)).app
            (formsSingleModules f p, formsSingleModules f p')))).hom
          ((Stacks.Cohomology.DerivedGlobalCupProduct.cupPairing
          (Stacks.Cohomology.DerivedGlobalCupProduct.cupProductOnSpace (inverseImageBase f))
          (DerivedCategory.Q.obj (formsSingleModules f p))
          (DerivedCategory.Q.obj (formsSingleModules f p')) q q').hom (ξ ⊗ₜ ζ))))) :=
    congrArg _ ((Stacks.Cohomology.HomologyPullback.map_map_comp_apply _ _ _ _ _).trans
      (Stacks.Cohomology.HomologyPullback.map_map_comp_apply _ _ _ _ _))
  have e2 := congrArg (fun φ => (lerayCohomologyIso g₀ (DerivedCategory.Q.obj
      (formsSingleModules f' (p + p'))) (q + q')).hom (((DerivedCategory.homologyFunctor
      (ModuleCat.{u} (baseRing (inverseImageBase f))) (q + q')).map
      ((baseSections (inverseImageBase f)).map φ)).hom
      ((Stacks.Cohomology.DerivedGlobalCupProduct.cupPairing
          (Stacks.Cohomology.DerivedGlobalCupProduct.cupProductOnSpace (inverseImageBase f))
          (DerivedCategory.Q.obj (formsSingleModules f p))
          (DerivedCategory.Q.obj (formsSingleModules f p')) q q').hom (ξ ⊗ₜ ζ))))
    (formsComparisonQ_multiplicative g' f' f g w p p')
  have e3 : (lerayCohomologyIso g₀ (DerivedCategory.Q.obj (formsSingleModules f' (p + p')))
      (q + q')).hom (((DerivedCategory.homologyFunctor (ModuleCat.{u}
      (baseRing (inverseImageBase f))) (q + q')).map ((baseSections (inverseImageBase f)).map
      (((Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
          (inverseImageBase f).sheaf)).map (formsComparisonQ g' f' f g w p ×ₘ formsComparisonQ g' f'
              f g w p')) ≫ (relativeCupProduct g₀ (DerivedCategory.Q.obj (formsSingleModules f' p))
          (DerivedCategory.Q.obj (formsSingleModules f' p'))) ≫
              ((derivedPushforward g₀).map (((derivedToTensorNatTrans (inverseImageBase f')).app
              (formsSingleModules f' p, formsSingleModules f' p')) ≫
              (DerivedCategory.Q.map (formsSingleWedge f' p p'))))))).hom
        ((Stacks.Cohomology.DerivedGlobalCupProduct.cupPairing
          (Stacks.Cohomology.DerivedGlobalCupProduct.cupProductOnSpace (inverseImageBase f))
          (DerivedCategory.Q.obj (formsSingleModules f p))
          (DerivedCategory.Q.obj (formsSingleModules f p')) q q').hom (ξ ⊗ₜ ζ))) =
      (lerayCohomologyIso g₀ (DerivedCategory.Q.obj (formsSingleModules f' (p + p'))) (q + q')).hom
          (((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing (inverseImageBase f)))
          (q + q')).map ((baseSections (inverseImageBase f)).map
          ((derivedPushforward g₀).map (((derivedToTensorNatTrans (inverseImageBase f')).app
          (formsSingleModules f' p, formsSingleModules f' p')) ≫
          (DerivedCategory.Q.map (formsSingleWedge f' p p')))))).hom
          (((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing (inverseImageBase f)))
          (q + q')).map ((baseSections (inverseImageBase f)).map
          (relativeCupProduct g₀ (DerivedCategory.Q.obj (formsSingleModules f' p))
          (DerivedCategory.Q.obj (formsSingleModules f' p'))))).hom
        (((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing (inverseImageBase f)))
            (q + q')).map ((baseSections (inverseImageBase f)).map
            ((Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
          (inverseImageBase f).sheaf)).map (formsComparisonQ g' f' f g w p ×ₘ formsComparisonQ g' f'
              f g w p')))).hom ((Stacks.Cohomology.DerivedGlobalCupProduct.cupPairing
          (Stacks.Cohomology.DerivedGlobalCupProduct.cupProductOnSpace (inverseImageBase f))
          (DerivedCategory.Q.obj (formsSingleModules f p))
          (DerivedCategory.Q.obj (formsSingleModules f p')) q q').hom (ξ ⊗ₜ ζ))))) :=
    congrArg _ ((Stacks.Cohomology.HomologyPullback.map_map_comp_apply _ _ _ _ _).trans
      (Stacks.Cohomology.HomologyPullback.map_map_comp_apply _ _ _ _ _))
  have e4 := Stacks.Cohomology.DerivedGlobalCupProduct.cupPairing_naturality_apply
    (Stacks.Cohomology.DerivedGlobalCupProduct.cupProductOnSpace (inverseImageBase f))
    (formsComparisonQ g' f' f g w p) (formsComparisonQ g' f' f g w p') q q' ξ ζ
  have e5 := Stacks.Cohomology.LerayCupPairing.lerayCohomologyIso_naturality_apply g₀
    (((derivedToTensorNatTrans (inverseImageBase f')).app (formsSingleModules f' p,
        formsSingleModules f' p')) ≫ (DerivedCategory.Q.map (formsSingleWedge f' p p'))) (q + q')
        (((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing (inverseImageBase f)))
        (q + q')).map ((baseSections (inverseImageBase f)).map
        (relativeCupProduct g₀ (DerivedCategory.Q.obj (formsSingleModules f' p))
          (DerivedCategory.Q.obj (formsSingleModules f' p'))))).hom
              ((Stacks.Cohomology.DerivedGlobalCupProduct.cupPairing
      (Stacks.Cohomology.DerivedGlobalCupProduct.cupProductOnSpace (inverseImageBase f)) _ _ q
          q').hom
      (((DerivedCategory.homologyFunctor _ q).map ((baseSections (inverseImageBase f)).map
          (formsComparisonQ g' f' f g w p))).hom ξ ⊗ₜ
        ((DerivedCategory.homologyFunctor _ q').map ((baseSections (inverseImageBase f)).map
            (formsComparisonQ g' f' f g w p'))).hom ζ)))
  have e6 := Stacks.Cohomology.LerayCupPairing.lerayCohomologyIso_relativeCupProduct_cupPairing
    g₀ (DerivedCategory.Q.obj (formsSingleModules f' p))
    (DerivedCategory.Q.obj (formsSingleModules f' p')) q q'
    (((DerivedCategory.homologyFunctor _ q).map ((baseSections (inverseImageBase f)).map
        (formsComparisonQ g' f' f g w p))).hom ξ)
    (((DerivedCategory.homologyFunctor _ q').map ((baseSections (inverseImageBase f)).map
        (formsComparisonQ g' f' f g w p'))).hom ζ)
  have e7 := Stacks.Cohomology.HomologyPullback.map_map_comp_apply
      (baseSections (inverseImageBase f')) (DerivedCategory.homologyFunctor
      (ModuleCat.{u} (baseRing (inverseImageBase f'))) (q + q'))
      ((derivedToTensorNatTrans (inverseImageBase f')).app (formsSingleModules f' p,
      formsSingleModules f' p')) (DerivedCategory.Q.map (formsSingleWedge f' p p'))
    ((Stacks.Cohomology.DerivedGlobalCupProduct.cupPairing
      (Stacks.Cohomology.DerivedGlobalCupProduct.cupProductOnSpace (inverseImageBase f')) _ _ q
          q').hom
      ((lerayCohomologyIso g₀ _ q).hom (((DerivedCategory.homologyFunctor _ q).map
        ((baseSections (inverseImageBase f)).map (formsComparisonQ g' f' f g w p))).hom ξ) ⊗ₜ
      (lerayCohomologyIso g₀ _ q').hom (((DerivedCategory.homologyFunctor _ q').map
        ((baseSections (inverseImageBase f)).map (formsComparisonQ g' f' f g w p'))).hom ζ)))
  refine e1.symm.trans (e2.trans (e3.trans ?_))
  refine (congrArg (fun z => (lerayCohomologyIso g₀ (DerivedCategory.Q.obj
      (formsSingleModules f' (p + p'))) (q + q')).hom (((DerivedCategory.homologyFunctor
      (ModuleCat.{u} (baseRing (inverseImageBase f))) (q + q')).map
      ((baseSections (inverseImageBase f)).map ((derivedPushforward g₀).map
      (((derivedToTensorNatTrans (inverseImageBase f')).app (formsSingleModules f' p,
      formsSingleModules f' p')) ≫ (DerivedCategory.Q.map (formsSingleWedge f' p p')))))).hom
    (((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing (inverseImageBase f))) (q + q')).map
        ((baseSections (inverseImageBase f)).map (relativeCupProduct g₀
        (DerivedCategory.Q.obj (formsSingleModules f' p))
          (DerivedCategory.Q.obj (formsSingleModules f' p'))))).hom z))) e4.symm).trans ?_
  exact e5.trans ((congrArg (fun z => ((DerivedCategory.homologyFunctor
      (ModuleCat.{u} (baseRing (inverseImageBase f'))) (q + q')).map
      ((baseSections (inverseImageBase f')).map
        ((derivedToTensorNatTrans (inverseImageBase f')).app
          (formsSingleModules f' p, formsSingleModules f' p') ≫
        DerivedCategory.Q.map (formsSingleWedge f' p p')))).hom z) e6).trans e7)

/-- **The pullback sends the unit to the unit**: `g'^*1 = 1` in `H^0(X', Ω^0_{X'/S'})`, since the
pullback of the global function `1` is `1`. -/
theorem hodgePullback_hodgeOne :
    hodgePullback g' f' f g w 0 0 (hodgeOne (formsAlgebras f)) =
      hodgeOne (formsAlgebras f') := by
  refine (congrArg (fun t => hodgePullback g' f' f g w 0 0 t)
    (hodgeOne_eq_globalClass (formsAlgebras f))).trans ?_
  refine Eq.trans ?_ (hodgeOne_eq_globalClass (formsAlgebras f')).symm
  refine cohomologyPullback_globalClass g₀
    (formsSinglePushforward g' f' f g w 0) 0 (formsOneCycle _) (formsOneCycle _) ?_
  refine (ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i
    (((Stacks.Cohomology.DerivedGlobalCupProduct.globalSections
      (inverseImageBase f)).mapHomologicalComplex (up ℤ)).map
        (formsSinglePushforward g' f' f g w 0)) 0) (formsOneCycle _)).trans ?_
  refine
      (congrArg
      (fun t => ConcreteCategory.hom ((((Stacks.Cohomology.DerivedGlobalCupProduct.globalSections
      (inverseImageBase f)).mapHomologicalComplex (up ℤ)).map
        (formsSinglePushforward g' f' f g w 0)).f 0) t)
    (iCycles_formsOneCycle (formsAlgebras f))).trans ?_
  refine Eq.trans ?_ (iCycles_formsOneCycle (formsAlgebras f')).symm
  exact (formsSinglePushforward_f_zero_val_app g' f' f g w 0 (op ⊤) _).trans
    (Scheme.Hom.relativeDifferentialFormsPullback_one g' f f' g w ⊤)

end Hodge


/-! ### The pullback on `H^*_{Hodge}` -/

section Algebra

variable {X X' S S' : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
  (w : g' ≫ f = f' ≫ g)

/-- The ring `Γ(X, f⁻¹𝒪_S)` of global sections of the base ring sheaf of `f : X ⟶ S`, over which
the Hodge cohomology groups `H^q(X, Ω^p_{X/S})` are modules. -/
abbrev hodgeBaseRing (f : X ⟶ S) : RingCat.{u} :=
  (AlgebraicGeometry.SheafOfModules.underlyingRingSheaf
    ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf)).obj.obj (op ⊤)

/-- **Pullback is compatible with the cup product on Hodge cohomology** (Section 50.5):
`g'^*(ξ ∪ ζ) = g'^*ξ ∪ g'^*ζ` for `ξ ∈ H^q(X, Ω^p_{X/S})` and `ζ ∈ H^{q'}(X, Ω^{p'}_{X/S})`, the
product read in bidegree `(p + p', q + q')`. -/
theorem hodgePullback_hodgeCohomologyCup (p p' : ℕ) (q q' : ℤ)
    (ξ : hodgeCohomologyComponent (formsAlgebras f) p q)
    (ζ : hodgeCohomologyComponent (formsAlgebras f) p' q') :
    hodgePullback g' f' f g w (p + p') (q + q')
        (hodgeCohomologyCup (formsAlgebras f) p p' q q' ξ ζ) =
      hodgeCohomologyCup (formsAlgebras f') p p' q q'
        (hodgePullback g' f' f g w p q ξ) (hodgePullback g' f' f g w p' q' ζ) :=
  (map_zsmul (hodgePullback g' f' f g w (p + p') (q + q')) (((q * (p' : ℤ)).negOnePow : ℤ))
    (hodgeComponentCup (formsAlgebras f)
      (AlgebraicGeometry.SheafOfModules.exteriorProductComponent (formsAlgebras f) p p')
        q q' ξ ζ)).trans
    (congrArg ((((q * (p' : ℤ)).negOnePow : ℤ)) • ·)
      (hodgePullback_hodgeComponentCup g' f' f g w p p' q q' ξ ζ))

/-- The pullback commutes with reading a class in an equal cohomological degree. -/
theorem hodgePullback_reindexHodgeDeg {p : ℕ} {q q' : ℤ} (h : q = q')
    (x : hodgeCohomologyComponent (formsAlgebras f) p q) :
    hodgePullback g' f' f g w p q' (reindexHodgeDeg (formsAlgebras f) h x) =
      reindexHodgeDeg (formsAlgebras f') h (hodgePullback g' f' f g w p q x) := by
  subst h
  rfl

/-- **The pullback `H^n_{Hodge}(X/S) ⟶ H^n_{Hodge}(X'/S')`** of a commutative square, the pullback
`hodgePullback` on each summand `H^q(X, Ω^p_{X/S})`. -/
def hodgePiecePullback (n : ℤ) :
    hodgePiece (formsAlgebras f) n →+ hodgePiece (formsAlgebras f') n :=
  DirectSum.map fun i => (hodgePullback g' f' f g w i.1.1 (i.1.2 : ℤ)).toAddMonoidHom

/-- On a class of pure bidegree the pullback on `H^n_{Hodge}` is the pullback `hodgePullback`. -/
theorem hodgePiecePullback_of (n : ℤ) (i : HodgeBidegreeInt n)
    (x : hodgeCohomologyComponent (formsAlgebras f) i.1.1 (i.1.2 : ℤ)) :
    hodgePiecePullback g' f' f g w n (DirectSum.of _ i x) =
      DirectSum.of (fun k : HodgeBidegreeInt n =>
          (hodgeCohomologyComponent (formsAlgebras f') k.1.1 (k.1.2 : ℤ) : Type u)) i
        (hodgePullback g' f' f g w i.1.1 (i.1.2 : ℤ) x) :=
  DirectSum.map_of (fun i : HodgeBidegreeInt n =>
    (hodgePullback g' f' f g w i.1.1 (i.1.2 : ℤ)).toAddMonoidHom) i x

/-- The pullback on `H^n_{Hodge}` is semilinear over the ring map of the square. -/
theorem hodgePiecePullback_smul (n : ℤ) (a : hodgeBaseRing f)
    (x : hodgePiece (formsAlgebras f) n) :
    hodgePiecePullback g' f' f g w n (a • x) =
      hodgeBaseRingHom g' f' f g w a • hodgePiecePullback g' f' f g w n x := by
  induction x using DirectSum.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | add x x' hx hx' => rw [smul_add, map_add, map_add, hx, hx', smul_add]
  | of i ξ =>
    exact (congrArg (hodgePiecePullback g' f' f g w n) (DirectSum.of_smul _ i a ξ).symm).trans
      ((hodgePiecePullback_of g' f' f g w n i (a • ξ)).trans
        ((congrArg (DirectSum.of (fun k : HodgeBidegreeInt n => (hodgeCohomologyComponent
            (formsAlgebras f') k.1.1 (k.1.2 : ℤ) : Type u)) i)
          ((hodgePullback g' f' f g w i.1.1 (i.1.2 : ℤ)).map_smulₛₗ a ξ)).trans
          ((DirectSum.of_smul _ i _ _).trans
            (congrArg (hodgeBaseRingHom g' f' f g w a • ·)
              (hodgePiecePullback_of g' f' f g w n i ξ).symm))))

/-- **The pullback is multiplicative on `H^*_{Hodge}`**: `g'^*(x ∪ y) = g'^*x ∪ g'^*y` for
`x ∈ H^n_{Hodge}(X/S)` and `y ∈ H^m_{Hodge}(X/S)`. -/
theorem hodgePiecePullback_mul (n m : ℤ) (x : hodgePiece (formsAlgebras f) n)
    (y : hodgePiece (formsAlgebras f) m) :
    hodgePiecePullback g' f' f g w (n + m) (hodgePieceMul _ n m x y) =
      hodgePieceMul _ n m (hodgePiecePullback g' f' f g w n x)
        (hodgePiecePullback g' f' f g w m y) := by
  induction x using DirectSum.induction_on with
  | zero => simp only [map_zero, AddMonoidHom.zero_apply]
  | add x x' hx hx' => simp only [map_add, AddMonoidHom.add_apply, hx, hx']
  | of i ξ =>
  induction y using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | add y y' hy hy' => simp only [map_add, hy, hy']
  | of j ζ =>
  exact (congrArg (hodgePiecePullback g' f' f g w (n + m))
      (hodgePieceMul_of (formsAlgebras f) i j ξ ζ)).trans
    ((hodgePiecePullback_of g' f' f g w (n + m) _ _).trans
      ((congrArg (DirectSum.of (fun k : HodgeBidegreeInt (n + m) => (hodgeCohomologyComponent
          (formsAlgebras f') k.1.1 (k.1.2 : ℤ) : Type u)) ⟨_, hodgeBidegreeInt_add i j⟩)
        ((hodgePullback_reindexHodgeDeg g' f' f g w _ _).trans
        (congrArg (reindexHodgeDeg (formsAlgebras f') _)
          (hodgePullback_hodgeCohomologyCup g' f' f g w _ _ _ _ ξ ζ)))).trans
        ((hodgePieceMul_of (formsAlgebras f') i j _ _).symm.trans
          (congrArg₂ (fun a b => hodgePieceMul (formsAlgebras f') n m a b)
            (hodgePiecePullback_of g' f' f g w n i ξ).symm
            (hodgePiecePullback_of g' f' f g w m j ζ).symm))))

/-- The pullback on `H^0_{Hodge}` sends the unit to the unit. -/
theorem hodgePiecePullback_one :
    hodgePiecePullback g' f' f g w 0 (hodgePieceOne (formsAlgebras f)) =
      hodgePieceOne (formsAlgebras f') :=
  (hodgePiecePullback_of g' f' f g w 0 ⟨(0, 0), rfl⟩ (hodgeOne (formsAlgebras f))).trans
    (congrArg (DirectSum.of (fun k : HodgeBidegreeInt 0 => (hodgeCohomologyComponent
        (formsAlgebras f') k.1.1 (k.1.2 : ℤ) : Type u)) ⟨(0, 0), rfl⟩)
        (hodgePullback_hodgeOne g' f' f g w))

/-- **The pullback `g'^* : H^*_{Hodge}(X/S) ⟶ H^*_{Hodge}(X'/S')` is a homomorphism of rings.** -/
def hodgeAlgebraPullback :
    hodgeAlgebra (formsAlgebras f) →+* hodgeAlgebra (formsAlgebras f') :=
  DirectSum.toSemiring
    (fun n => (DirectSum.of (hodgePiece (formsAlgebras f')) n).comp
      (hodgePiecePullback g' f' f g w n))
    (by
      change DirectSum.of (hodgePiece (formsAlgebras f')) 0
        (hodgePiecePullback g' f' f g w 0 (hodgePieceOne _)) = 1
      rw [hodgePiecePullback_one]
      rfl)
    (fun {i j} x y => by
      change DirectSum.of (hodgePiece (formsAlgebras f')) (i + j)
          (hodgePiecePullback g' f' f g w (i + j)
          (hodgePieceMul _ i j x y)) = _
      rw [hodgePiecePullback_mul]
      exact (hodgeAlgebra_of_mul_of _ _ _).symm)

/-- On a homogeneous class the pullback on `H^*_{Hodge}` is the pullback on `H^n_{Hodge}`. -/
theorem hodgeAlgebraPullback_of (n : ℤ) (x : hodgePiece (formsAlgebras f) n) :
    hodgeAlgebraPullback g' f' f g w (DirectSum.of (hodgePiece (formsAlgebras f)) n x) =
      DirectSum.of (hodgePiece (formsAlgebras f')) n (hodgePiecePullback g' f' f g w n x) :=
  DirectSum.toSemiring_of _ _ _ n x

/-- **The pullback preserves the grading**: it carries `H^n_{Hodge}(X/S)` into
`H^n_{Hodge}(X'/S')`. -/
theorem hodgeAlgebraPullback_mem_hodgeGrade {k : Type*} [CommRing k]
    (σ : k →+* hodgeBaseRing f) (σ' : k →+* hodgeBaseRing f') (n : ℤ)
    (a : hodgeAlgebra (formsAlgebras f)) (ha : a ∈ hodgeGrade (formsAlgebras f) σ n) :
    hodgeAlgebraPullback g' f' f g w a ∈ hodgeGrade (formsAlgebras f') σ' n := by
  obtain ⟨x, rfl⟩ := (mem_hodgeGrade (formsAlgebras f) σ n a).1 ha
  rw [hodgeAlgebraPullback_of]
  exact of_mem_hodgeGrade (formsAlgebras f') σ' n _

/-- The pullback of the class `σ(c) · 1` of a scalar is the class `σ'(c) · 1`, for ring maps
`σ`, `σ'` from `k` compatible with the ring map of the square. -/
theorem hodgeAlgebraPullback_scalarClass {k : Type*} [CommRing k]
    (σ : k →+* hodgeBaseRing f) (σ' : k →+* hodgeBaseRing f')
    (hσ : (hodgeBaseRingHom g' f' f g w).comp σ = σ') (c : k) :
    hodgeAlgebraPullback g' f' f g w
        (DirectSum.of (hodgePiece (formsAlgebras f)) 0 (σ c • hodgePieceOne _)) =
      DirectSum.of (hodgePiece (formsAlgebras f')) 0 (σ' c • hodgePieceOne _) := by
  rw [hodgeAlgebraPullback_of, hodgePiecePullback_smul, hodgePiecePullback_one, ← hσ]
  rfl

/-- **The pullback is a homomorphism of `k`-algebras**, for ring maps `σ : k ⟶ Γ(X, f⁻¹𝒪_S)` and
`σ' : k ⟶ Γ(X', f'⁻¹𝒪_{S'})` compatible with the ring map of the square. -/
def hodgeAlgebraPullbackAlgHom {k : Type*} [CommRing k] (σ : k →+* hodgeBaseRing f)
    (σ' : k →+* hodgeBaseRing f') (hσ : (hodgeBaseRingHom g' f' f g w).comp σ = σ') :
    letI := hodgeAlgebraAlgebra (formsAlgebras f) σ
    letI := hodgeAlgebraAlgebra (formsAlgebras f') σ'
    hodgeAlgebra (formsAlgebras f) →ₐ[k] hodgeAlgebra (formsAlgebras f') :=
  letI : ∀ n, Module k (hodgePiece (formsAlgebras f) n) := hodgePieceModule _ σ
  letI : ∀ n, Module k (hodgePiece (formsAlgebras f') n) := hodgePieceModule _ σ'
  letI := hodgeGAlgebra (formsAlgebras f) σ
  letI := hodgeGAlgebra (formsAlgebras f') σ'
  { toRingHom := hodgeAlgebraPullback g' f' f g w
    commutes' := fun c =>
      (congrArg (hodgeAlgebraPullback g' f' f g w)
          (DirectSum.algebraMap_apply k (hodgePiece (formsAlgebras f)) c)).trans
        ((hodgeAlgebraPullback_scalarClass g' f' f g w σ σ' hσ c).trans
          (DirectSum.algebraMap_apply k (hodgePiece (formsAlgebras f')) c).symm) }

/-- The `k`-algebra homomorphism is the ring homomorphism `hodgeAlgebraPullback`. -/
theorem hodgeAlgebraPullbackAlgHom_apply {k : Type*} [CommRing k]
    (σ : k →+* hodgeBaseRing f) (σ' : k →+* hodgeBaseRing f')
    (hσ : (hodgeBaseRingHom g' f' f g w).comp σ = σ') (a : hodgeAlgebra (formsAlgebras f)) :
    hodgeAlgebraPullbackAlgHom g' f' f g w σ σ' hσ a = hodgeAlgebraPullback g' f' f g w a :=
  rfl

/-- The identity square induces the identity on `H^n_{Hodge}(X/S)`. -/
theorem hodgePiecePullback_id (f : X ⟶ S) (w : 𝟙 X ≫ f = f ≫ 𝟙 S) (n : ℤ)
    (x : hodgePiece (formsAlgebras f) n) :
    hodgePiecePullback (𝟙 X) f f (𝟙 S) w n x = x := by
  induction x using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | add x x' hx hx' => rw [map_add, hx, hx']
  | of i ξ =>
    exact (hodgePiecePullback_of (𝟙 X) f f (𝟙 S) w n i ξ).trans
      (congrArg (DirectSum.of (fun k : HodgeBidegreeInt n => (hodgeCohomologyComponent
          (formsAlgebras f) k.1.1 (k.1.2 : ℤ) : Type u)) i) (hodgePullback_id f w _ _ ξ))

/-- **The identity square induces the identity on `H^*_{Hodge}(X/S)`.** -/
theorem hodgeAlgebraPullback_id (f : X ⟶ S) (w : 𝟙 X ≫ f = f ≫ 𝟙 S) :
    hodgeAlgebraPullback (𝟙 X) f f (𝟙 S) w = RingHom.id _ :=
  DirectSum.ringHom_ext fun n x => by
    rw [hodgeAlgebraPullback_of, hodgePiecePullback_id]
    rfl

section Comp

variable {X'' S'' : Scheme.{u}} (g'' : X'' ⟶ X') (f'' : X'' ⟶ S'') (h : S'' ⟶ S')
  (w' : g'' ≫ f' = f'' ≫ h) (w'' : (g'' ≫ g') ≫ f = f'' ≫ (h ≫ g))

/-- Pasting two squares induces the composite of the pullbacks on `H^n_{Hodge}`. -/
theorem hodgePiecePullback_comp (n : ℤ) (x : hodgePiece (formsAlgebras f) n) :
    hodgePiecePullback (g'' ≫ g') f'' f (h ≫ g) w'' n x =
      hodgePiecePullback g'' f'' f' h w' n (hodgePiecePullback g' f' f g w n x) := by
  induction x using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | add x x' hx hx' => rw [map_add, hx, hx', map_add, map_add]
  | of i ξ =>
    exact (hodgePiecePullback_of _ _ _ _ w'' n i ξ).trans
      ((congrArg (DirectSum.of (fun k : HodgeBidegreeInt n => (hodgeCohomologyComponent
          (formsAlgebras f'') k.1.1 (k.1.2 : ℤ) : Type u)) i)
          (hodgePullback_comp g' f' f g w g'' f'' h w' w'' _ _ ξ)).trans
        ((hodgePiecePullback_of g'' f'' f' h w' n i _).symm.trans
          (congrArg (hodgePiecePullback g'' f'' f' h w' n)
            (hodgePiecePullback_of g' f' f g w n i ξ).symm)))

/-- **Pasting two squares induces the composite of the pullbacks on `H^*_{Hodge}`.** -/
theorem hodgeAlgebraPullback_comp :
    hodgeAlgebraPullback (g'' ≫ g') f'' f (h ≫ g) w'' =
      (hodgeAlgebraPullback g'' f'' f' h w').comp (hodgeAlgebraPullback g' f' f g w) :=
  DirectSum.ringHom_ext fun n x => by
    rw [RingHom.comp_apply, hodgeAlgebraPullback_of, hodgeAlgebraPullback_of,
      hodgeAlgebraPullback_of, hodgePiecePullback_comp g' f' f g w g'' f'' h w' w'']

end Comp

/-! ### Schemes over a fixed base -/

variable {k : Type*} [CommRing k] (τ : k →+* S.sheaf.obj.obj (op ⊤))

/-- The scalars `k ⟶ Γ(X, p⁻¹𝒪_S)` of an `S`-scheme `p : X ⟶ S`, for a ring map
`τ : k ⟶ Γ(S, 𝒪_S)`: `τ` followed by the map from the global sections of `S`. For `S = Spec k`
and `τ` the inverse of `Γ(Spec k, 𝒪) ≅ k` this is the `k`-structure of Hodge cohomology over
`k`. -/
abbrev hodgeScalars (p : X ⟶ S) :
    k →+* hodgeBaseRing p :=
  (Scheme.Hom.inverseImageGlobalSections p).hom.comp τ

/-- For a morphism of `S`-schemes the ring map of its square is compatible with the scalars. -/
theorem hodgeBaseRingHom_comp_hodgeScalars (fX : X ⟶ S) (fX' : X' ⟶ S)
    (w : g' ≫ fX = fX' ≫ 𝟙 S) :
    (hodgeBaseRingHom g' fX' fX (𝟙 S) w).comp (hodgeScalars τ fX) = hodgeScalars τ fX' :=
  (RingHom.comp_assoc _ _ _).symm.trans (congrArg (fun φ => φ.comp τ)
    (hodgeBaseRingHom_comp_inverseImageGlobalSections_overBase g' fX fX' w))

/-- **The pullback along a morphism of `S`-schemes, as a homomorphism of `k`-algebras**
`g'^* : H^*_{Hodge}(X/S) ⟶ H^*_{Hodge}(X'/S)`, `k` acting through `τ : k ⟶ Γ(S, 𝒪_S)`. -/
def hodgeAlgebraPullbackOverBase (fX : X ⟶ S) (fX' : X' ⟶ S) (w : g' ≫ fX = fX' ≫ 𝟙 S) :
    letI := hodgeAlgebraAlgebra (formsAlgebras fX) (hodgeScalars τ fX)
    letI := hodgeAlgebraAlgebra (formsAlgebras fX') (hodgeScalars τ fX')
    hodgeAlgebra (formsAlgebras fX) →ₐ[k] hodgeAlgebra (formsAlgebras fX') :=
  hodgeAlgebraPullbackAlgHom g' fX' fX (𝟙 S) w _ _
    (hodgeBaseRingHom_comp_hodgeScalars g' τ fX fX' w)

/-- The `k`-algebra homomorphism of a morphism of `S`-schemes is the ring homomorphism
`hodgeAlgebraPullback` of its square. -/
theorem hodgeAlgebraPullbackOverBase_apply (fX : X ⟶ S) (fX' : X' ⟶ S)
    (w : g' ≫ fX = fX' ≫ 𝟙 S) (a : hodgeAlgebra (formsAlgebras fX)) :
    hodgeAlgebraPullbackOverBase g' τ fX fX' w a = hodgeAlgebraPullback g' fX' fX (𝟙 S) w a :=
  rfl

/-- **The identity induces the identity of `k`-algebras** (datum (D1), `pull_id`). -/
theorem hodgeAlgebraPullbackOverBase_id (fX : X ⟶ S) (w : 𝟙 X ≫ fX = fX ≫ 𝟙 S) :
    letI := hodgeAlgebraAlgebra (formsAlgebras fX) (hodgeScalars τ fX)
    hodgeAlgebraPullbackOverBase (𝟙 X) τ fX fX w = AlgHom.id k _ := by
  let := hodgeAlgebraAlgebra (formsAlgebras fX) (hodgeScalars τ fX)
  refine AlgHom.ext fun a => ?_
  rw [hodgeAlgebraPullbackOverBase_apply, hodgeAlgebraPullback_id]
  rfl

/-- **Composites of morphisms of `S`-schemes induce composites of `k`-algebra homomorphisms**
(datum (D1), `pull_comp`): `(g'' ≫ g')^* = g''^* ∘ g'^*`. -/
theorem hodgeAlgebraPullbackOverBase_comp {X'' : Scheme.{u}} (fX : X ⟶ S) (fX' : X' ⟶ S)
    (fX'' : X'' ⟶ S) (g'' : X'' ⟶ X') (w : g' ≫ fX = fX' ≫ 𝟙 S)
    (w' : g'' ≫ fX' = fX'' ≫ 𝟙 S) (w'' : (g'' ≫ g') ≫ fX = fX'' ≫ 𝟙 S) :
    letI := hodgeAlgebraAlgebra (formsAlgebras fX) (hodgeScalars τ fX)
    letI := hodgeAlgebraAlgebra (formsAlgebras fX') (hodgeScalars τ fX')
    letI := hodgeAlgebraAlgebra (formsAlgebras fX'') (hodgeScalars τ fX'')
    hodgeAlgebraPullbackOverBase (g'' ≫ g') τ fX fX'' w'' =
      (hodgeAlgebraPullbackOverBase g'' τ fX' fX'' w').comp
        (hodgeAlgebraPullbackOverBase g' τ fX fX' w) := by
  let := hodgeAlgebraAlgebra (formsAlgebras fX) (hodgeScalars τ fX)
  let := hodgeAlgebraAlgebra (formsAlgebras fX') (hodgeScalars τ fX')
  let := hodgeAlgebraAlgebra (formsAlgebras fX'') (hodgeScalars τ fX'')
  have hring : hodgeAlgebraPullback (g'' ≫ g') fX'' fX (𝟙 S) w'' =
      (hodgeAlgebraPullback g'' fX'' fX' (𝟙 S) w').comp
        (hodgeAlgebraPullback g' fX' fX (𝟙 S) w) :=
    hodgeAlgebraPullback_comp g' fX' fX (𝟙 S) w g'' fX'' (𝟙 S) w' w''
  refine AlgHom.ext fun a => ?_
  rw [AlgHom.comp_apply, hodgeAlgebraPullbackOverBase_apply, hodgeAlgebraPullbackOverBase_apply,
    hodgeAlgebraPullbackOverBase_apply, hring, RingHom.comp_apply]

/-- **The pullback along a morphism of `S`-schemes preserves the grading** (datum (D1),
`pull_grade`). -/
theorem hodgeAlgebraPullbackOverBase_mem_hodgeGrade (fX : X ⟶ S) (fX' : X' ⟶ S)
    (w : g' ≫ fX = fX' ≫ 𝟙 S) (n : ℤ) (a : hodgeAlgebra (formsAlgebras fX))
    (ha : a ∈ hodgeGrade (formsAlgebras fX) (hodgeScalars τ fX) n) :
    hodgeAlgebraPullbackOverBase g' τ fX fX' w a ∈
      hodgeGrade (formsAlgebras fX') (hodgeScalars τ fX') n :=
  hodgeAlgebraPullback_mem_hodgeGrade g' fX' fX (𝟙 S) w (hodgeScalars τ fX) (hodgeScalars τ fX')
    n a ha

end Algebra


end Stacks.HodgeWeil

end
