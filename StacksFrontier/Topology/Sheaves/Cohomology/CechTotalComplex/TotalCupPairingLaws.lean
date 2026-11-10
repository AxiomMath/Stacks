module

public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.GlobalCupProductShift
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TensorComplex.AssociatorOnLocalSections
public import StacksFrontier.Topology.Sheaves.Cohomology.MayerVietorisAndLimits.InverseSystemsOnASpace
public import StacksFrontier.Algebra.Homology.MapBifunctorHomotopyEquiv
public import StacksFrontier.AlgebraicGeometry.Cohomology.FlasqueReductionOfTheCupProductSquare
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafTensorPureTensors
import all StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.CupPairingNaturality

/-!
# Associativity and graded commutativity of the cup product on total tensor complexes

Let `(S, 𝒪_S)` be a ringed space and `A = Γ(S, 𝒪_S)`. For complexes `K`, `L` of `𝒪_S`-modules
the cup product of Cohomology, Section 0FKU followed by the canonical map from the derived to the
ordinary tensor product is a pairing

`∪ : Hⁱ(S, K) × Hʲ(S, L) ⟶ Hⁱ⁺ʲ(S, Tot(K ⊗_{𝒪_S} L))`

(`Stacks.Cohomology.DerivedGlobalCupProduct.totalCupPairing`). This file proves that it is
associative and graded commutative for the associativity and commutativity constraints of the
symmetric monoidal category of complexes of Tag 0FPQ, for bounded below complexes: these are the
two laws Cohomology, Lemmas 0FP4 and 0FP5 give the cup product, read on the total tensor
complexes through which every multiplication of complexes factors.

## Main definitions

* `Stacks.Cohomology.DerivedGlobalCupProduct.cupClass`: the cup product `ξ ∪ η`, read in an
  arbitrary target degree `n` with `i + j = n`, so that the two bracketings of a triple product
  live in the same module.
* `Stacks.Cohomology.DerivedGlobalCupProduct.tensorAssociator` and
  `Stacks.Cohomology.DerivedGlobalCupProduct.tensorBraiding`: the associator and the Koszul
  symmetry of Tag 0FPQ, at the spelling of iterated `HomologicalComplex.mapBifunctor`.
* `Stacks.Cohomology.DerivedGlobalCupProduct.cohomologyCast`: `Hᵃ(S, K) ⟶ Hᵇ(S, K)` for `a = b`.

## Main results

* `Stacks.Cohomology.DerivedGlobalCupProduct.cupClass_naturality`: the cup product is natural in
  chain maps of both complexes.
* `Stacks.Cohomology.DerivedGlobalCupProduct.cupClass_assoc`: **associativity**,
  `α((ξ ∪ η) ∪ ζ) = ξ ∪ (η ∪ ζ)`.
* `Stacks.Cohomology.DerivedGlobalCupProduct.cupClass_comm`: **graded commutativity**,
  `β(ξ ∪ η) = (-1)^{ij} η ∪ ξ`.
* `Stacks.Cohomology.FlasqueReduction.exists_stalk_homotopyEquiv_mapBifunctorMap`: a pair of
  stalkwise homotopy equivalences induces one on total tensor complexes.

## References

* [Stacks Project, Section 0FKU](https://stacks.math.columbia.edu/tag/0FKU)
* [Stacks Project, Tag 0FP4](https://stacks.math.columbia.edu/tag/0FP4)
* [Stacks Project, Tag 0FP5](https://stacks.math.columbia.edu/tag/0FP5)
* [Stacks Project, Tag 0FP3](https://stacks.math.columbia.edu/tag/0FP3)
* [Stacks Project, Tag 0FKV](https://stacks.math.columbia.edu/tag/0FKV)
* [Stacks Project, Tag 0FKT](https://stacks.math.columbia.edu/tag/0FKT)
* [Stacks Project, Tag 0FPQ](https://stacks.math.columbia.edu/tag/0FPQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open TopologicalSpace AlgebraicGeometry
open Stacks.Cohomology.GlobalKunneth
open Stacks.SheafOfModules.Tensor (ringSheaf sheafTensor)
open Stacks.Cohomology.DerivedSectionsLeray (sectionsUnitQ)
open RingTheory.TorProducts (cycleClass)
open scoped Stacks.Topology.SheafTensorAdditiveOnOpens TensorProduct

attribute [local instance_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf
attribute [local implicit_reducible] structureSheafRing Stacks.SheafOfModules.Tensor.ringSheaf

universe u

namespace Stacks.Cohomology.MonoidalComplexesOfModules

section

attribute [local instance] SheafOfModules.monoidalCategorySheafTensor
  SheafOfModules.symmetricCategorySheafTensor SheafOfModules.monoidalPreadditiveSheafTensor
  SheafOfModules.monoidalClosedSheafTensor
  SheafOfModules.preservesColimit_tensorRight_sheafTensor

universe v₀ u₀

variable {C : Type u₀} [Category.{v₀} C] {J : GrothendieckTopology C}
  (R : CategoryTheory.Sheaf J CommRingCat.{max u₀ v₀})

local instance : HasWeakSheafify J AddCommGrpCat.{max u₀ v₀} := inferInstance
local instance : J.WEqualsLocallyBijective AddCommGrpCat.{max u₀ v₀} := inferInstance
local instance : MonoidalCategory (Mod R) := SheafOfModules.monoidalCategorySheafTensor R
local instance : HasColimitsOfSize.{0, 0} (Mod R) := inferInstance

/-- **The commutativity constraint of the symmetric monoidal category of complexes of Tag 0FPQ on
a homogeneous summand**: on `Kᵖ ⊗ Lᵠ` it is the symmetry of `Mod(O)` times the Koszul sign
`(-1)^{pq}`, followed by the inclusion of `Lᵠ ⊗ Kᵖ`. -/
theorem ιTensorObj_braiding_hom_f (K L : Complexes R) (p q n : ℤ) (h : p + q = n) :
    letI := cochainComplexMonoidalCategory R
    letI := cochainComplexSymmetricCategory R
    HomologicalComplex.ιTensorObj K L p q n h ≫ (β_ K L).hom.f n =
      ((p * q).negOnePow : ℤˣ) • ((β_ (K.X p) (L.X q)).hom ≫
        HomologicalComplex.ιTensorObj L K q p n (by simpa [add_comm] using h)) :=
  CochainComplex.ιTensorObj_koszulBraiding K L p q n h

end

end Stacks.Cohomology.MonoidalComplexesOfModules

namespace Stacks.Cohomology.FlasqueReduction

open AlgebraicGeometry.SheafOfModules Stacks.SheafOfModules.KFlatStalkCriterion

variable {X : TopCat.{u}}
  (R : CategoryTheory.Sheaf.{u, u, u, u + 1} (Opens.grothendieckTopology X) CommRingCat.{u})

local instance (x : X) :
    (stalkFunctor (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x).Additive :=
  stalkFunctor_additive (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x

/-- **A pair of stalkwise homotopy equivalences induces one on total tensor complexes.** If the
stalk maps of `a : K ⟶ K'` and `b : L ⟶ L'` at every point are homotopy equivalences, so are the
stalk maps of `Tot(K ⊗_{𝒪_X} L) ⟶ Tot(K' ⊗_{𝒪_X} L')`. -/
theorem exists_stalk_homotopyEquiv_mapBifunctorMap
    {K K' L L' : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R)) ℤ}
    (a : K ⟶ K') (b : L ⟶ L')
    (ha : ∀ y : X, ∃ e : HomotopyEquiv (stalkComplex R y K) (stalkComplex R y K'),
      e.hom = stalkComplexMap R y a)
    (hb : ∀ y : X, ∃ e : HomotopyEquiv (stalkComplex R y L) (stalkComplex R y L'),
      e.hom = stalkComplexMap R y b) (y : X) :
    ∃ e : HomotopyEquiv
        (stalkComplex R y (HomologicalComplex.mapBifunctor K L
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R) (ComplexShape.up ℤ)))
        (stalkComplex R y (HomologicalComplex.mapBifunctor K' L'
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R) (ComplexShape.up ℤ))),
      e.hom = stalkComplexMap R y (HomologicalComplex.mapBifunctorMap a b
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R) (ComplexShape.up ℤ)) := by
  obtain ⟨ea, hea⟩ := ha y
  obtain ⟨eb, heb⟩ := hb y
  refine ⟨(HomotopyEquiv.ofIso (stalkTensorComplexIso R y K L)).trans
    ((HomologicalComplex.mapBifunctorHomotopyEquiv
      (MonoidalCategory.curriedTensor (ModuleCat.{u}
        (TopCat.Presheaf.stalk (C := RingCat.{u})
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R).obj y)))
      (ComplexShape.up ℤ) ea eb).trans
      (HomotopyEquiv.ofIso (stalkTensorComplexIso R y K' L').symm)), ?_⟩
  have hnat := stalkTensorComplexIso_hom_naturality R y a b
  change (stalkTensorComplexIso R y K L).hom ≫
      (HomologicalComplex.mapBifunctorMap ea.hom eb.hom _ _ ≫
        (stalkTensorComplexIso R y K' L').inv) = _
  rw [hea, heb, ← Category.assoc]
  refine (congrArg (· ≫ (stalkTensorComplexIso R y K' L').inv) hnat).symm.trans ?_
  exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (Iso.hom_inv_id _)).trans
    (Category.comp_id _))

end Stacks.Cohomology.FlasqueReduction

namespace Stacks.Cohomology.DerivedGlobalCupProduct

attribute [local instance] HasDerivedCategory.standard

variable {S : RingedSpace.{u, u}}

/-! ### Elementwise cup products with a free target degree -/

/-- The cohomology of `RΓ(S, -)` in degree `a`, read in an equal degree `b`. -/
def cohomologyCast (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing S))) {a b : ℤ}
    (h : a = b) : cohomologyModule K a ⟶ cohomologyModule K b :=
  eqToHom (congrArg (cohomologyModule K) h)

/-- The degree cast along `a = a` is the identity. -/
@[simp]
theorem cohomologyCast_rfl (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing S)))
    (a : ℤ) : cohomologyCast K (rfl : a = a) = 𝟙 _ :=
  rfl

/-- The map `Hⁿ(S, K) ⟶ Hⁿ(S, K')` induced by a chain map `f : K ⟶ K'`. -/
def cohomologyMap {K K' : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ}
    (f : K ⟶ K') (n : ℤ) :
    cohomologyModule (DerivedCategory.Q.obj K) n ⟶ cohomologyModule (DerivedCategory.Q.obj K') n :=
  (DerivedCategory.homologyFunctor _ n).map ((baseSections S).map (DerivedCategory.Q.map f))

/-- The degree cast commutes with the maps induced by chain maps. -/
theorem cohomologyCast_cohomologyMap
    {K K' : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ}
    (f : K ⟶ K') {a b : ℤ} (h : a = b) :
    cohomologyCast (DerivedCategory.Q.obj K) h ≫ cohomologyMap f b =
      cohomologyMap f a ≫ cohomologyCast (DerivedCategory.Q.obj K') h := by
  subst h
  simp

/-- **The cup product of two classes, in an arbitrary target degree**: for `ξ ∈ Hⁱ(S, K)`,
`η ∈ Hʲ(S, M)` and `i + j = n`, the class `ξ ∪ η ∈ Hⁿ(S, Tot(K ⊗ M))` of `totalCupPairing`, read
in degree `n`. -/
def cupClass (K M : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ)
    {i j n : ℤ} (h : i + j = n) (ξ : cohomologyModule (DerivedCategory.Q.obj K) i)
    (η : cohomologyModule (DerivedCategory.Q.obj M) j) :
    cohomologyModule (DerivedCategory.Q.obj
      (HomologicalComplex.mapBifunctor K M (sheafTensor S.sheaf) (ComplexShape.up ℤ))) n :=
  (cohomologyCast _ h).hom ((totalCupPairing K M i j).hom (ξ ⊗ₜ η))

/-- The identity chain map induces the identity. -/
@[simp]
theorem cohomologyMap_id_apply
    (K : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ) (n : ℤ)
    (x : cohomologyModule (DerivedCategory.Q.obj K) n) :
    (cohomologyMap (𝟙 K) n).hom x = x := by
  unfold cohomologyMap
  rw [DerivedCategory.Q.map_id, (baseSections S).map_id,
    (DerivedCategory.homologyFunctor _ n).map_id]
  rfl

variable (S) in
/-- **Derived global sections are additive**: `RΓ(S, -)` is an additive functor. -/
theorem additive_baseSections : (baseSections S).Additive := by
  have : (baseSections S).IsRightAdjoint :=
    (canonicalOnePointComparison S).adjunction.isRightAdjoint
  exact Functor.additive_of_preserves_binary_products _

/-- The map induced by a sum of chain maps is the sum of the induced maps. -/
theorem cohomologyMap_add
    {K K' : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ}
    (f g : K ⟶ K') (n : ℤ) : cohomologyMap (f + g) n = cohomologyMap f n + cohomologyMap g n := by
  have := additive_baseSections S
  unfold cohomologyMap
  rw [DerivedCategory.Q.map_add, (baseSections S).map_add,
    (DerivedCategory.homologyFunctor _ n).map_add]

/-- The map induced by an integer multiple of a chain map is that multiple of the induced map. -/
theorem cohomologyMap_zsmul
    {K K' : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ}
    (c : ℤ) (f : K ⟶ K') (n : ℤ) : cohomologyMap (c • f) n = c • cohomologyMap f n := by
  have := additive_baseSections S
  unfold cohomologyMap
  rw [DerivedCategory.Q.map_zsmul, (baseSections S).map_zsmul,
    (DerivedCategory.homologyFunctor _ n).map_zsmul]

/-- The degree cast commutes with the maps induced by chain maps, elementwise. -/
theorem cohomologyCast_cohomologyMap_apply
    {K K' : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ}
    (f : K ⟶ K') {a b : ℤ} (h : a = b) (x : cohomologyModule (DerivedCategory.Q.obj K) a) :
    (cohomologyCast (DerivedCategory.Q.obj K') h).hom ((cohomologyMap f a).hom x) =
      (cohomologyMap f b).hom ((cohomologyCast (DerivedCategory.Q.obj K) h).hom x) := by
  subst h
  rfl

/-- **The cup product is natural** in chain maps of both complexes. -/
theorem cupClass_naturality
    {K K' M M' : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ}
    (f : K ⟶ K') (g : M ⟶ M') {i j n : ℤ} (h : i + j = n)
    (ξ : cohomologyModule (DerivedCategory.Q.obj K) i)
    (η : cohomologyModule (DerivedCategory.Q.obj M) j) :
    (cohomologyMap (HomologicalComplex.mapBifunctorMap f g (sheafTensor S.sheaf)
        (ComplexShape.up ℤ)) n).hom (cupClass K M h ξ η) =
      cupClass K' M' h ((cohomologyMap f i).hom ξ) ((cohomologyMap g j).hom η) := by
  subst h
  have e := ConcreteCategory.congr_hom (totalCupPairing_naturality' f g i j
    (ModuleCat.ofHom (LinearMap.toSpanSingleton (baseRing S) _ ξ))
    (ModuleCat.ofHom (LinearMap.toSpanSingleton (baseRing S) _ η))) (1 : baseRing S)
  have e3 := (leftUnitor_inv_tensorHom_comp_apply_one _ _ _).symm.trans
    (e.trans (leftUnitor_inv_tensorHom_comp_apply_one _ _ (totalCupPairing K' M' i j)))
  simp only [cupClass, cohomologyCast_rfl, ModuleCat.hom_id]
  simp only [ConcreteCategory.comp_apply, ModuleCat.hom_ofHom, LinearMap.toSpanSingleton_apply,
    one_smul] at e3
  exact e3

/-- The degree cast of a cup product is the cup product read in the new degree. -/
theorem cohomologyCast_cupClass
    (K M : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ)
    {i j n n' : ℤ} (h : i + j = n) (h' : n = n')
    (ξ : cohomologyModule (DerivedCategory.Q.obj K) i)
    (η : cohomologyModule (DerivedCategory.Q.obj M) j) :
    (cohomologyCast _ h').hom (cupClass K M h ξ η) = cupClass K M (h.trans h') ξ η := by
  subst h h'
  rfl

/-! ### The cup product of two classes of global cocycles -/

variable (S) in
/-- The ringed site of opens of `S`, on which the local pure tensors of total tensor complexes
are formed. -/
abbrev spaceSite : AlgebraicGeometry.RingedSite.{u, u, u} :=
  Stacks.Cohomology.SpaceInverseSystems.ringedSiteOfSpace S

/-- The global section of `Kⁱ` underlying a global cocycle `z ∈ Zⁱ(Γ(S, K))`. -/
abbrev cocycleSection {K : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ}
    {i : ℤ} (z : ModuleCat.of (baseRing S) (baseRing S) ⟶ (sectionsComplex S K).cycles i) :
    (K.X i).val.obj (op ⊤) :=
  (z ≫ (sectionsComplex S K).iCycles i).hom (1 : baseRing S)

/-- A global cocycle is determined by its underlying global section. -/
theorem cocycle_ext {K : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ}
    {i : ℤ} {z z' : ModuleCat.of (baseRing S) (baseRing S) ⟶ (sectionsComplex S K).cycles i}
    (h : cocycleSection z = cocycleSection z') : z = z' := by
  rw [← cancel_mono ((sectionsComplex S K).iCycles i)]
  ext
  exact h

/-- The naive cup product of two global sections is their local pure tensor at `⊤`. -/
theorem naiveCupProductEval_f_ι_tmul
    (K M : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ) (i j n : ℤ)
    (h : i + j = n) (s : (K.X i).val.obj (op ⊤)) (t : (M.X j).val.obj (op ⊤)) :
    ((Stacks.Cech.SheafTensorPairing.naiveCupProductEval S.sheaf ⊤ K M).f n).hom
        ((HomologicalComplex.ιMapBifunctor
          (Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ K)
          (Stacks.Cech.SheafTensorPairing.evalComplex S.sheaf ⊤ M)
          (Stacks.Cech.CupProduct.tensorModules
            (Stacks.Cech.ModuleCupProduct.CoeffRing S.sheaf ⊤)) (ComplexShape.up ℤ) i j n h).hom
          (s ⊗ₜ t)) =
      AlgebraicGeometry.RingedSite.tensorComplexSection (spaceSite S) i j n h s t := by
  have e := ConcreteCategory.congr_hom
    (Stacks.Cech.SheafTensorPairing.ι_naiveCupProductEval_f S.sheaf ⊤ K M i j n h) (s ⊗ₜ t)
  exact e

/-- A chosen tensoring of cocycles of two complexes of global sections. -/
def tensorCycles (P Q : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ)
    (i j : ℤ) :
    (sectionsComplex S P).cycles i ⊗ (sectionsComplex S Q).cycles j ⟶
      (sectionsComplex S P ⊗ sectionsComplex S Q).cycles (i + j) :=
  (RingTheory.TorProducts.exists_tensorCycles (sectionsComplex S P) (sectionsComplex S Q)
    i j).choose

/-- The chosen tensoring of cocycles, followed by the inclusion of cocycles, is the tensor product
of the inclusions of cocycles followed by the inclusion of the summand of bidegree `(i, j)`. -/
theorem tensorCycles_iCycles
    (P Q : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ) (i j : ℤ) :
    tensorCycles P Q i j ≫ (sectionsComplex S P ⊗ sectionsComplex S Q).iCycles (i + j) =
      ((sectionsComplex S P).iCycles i ⊗ₘ (sectionsComplex S Q).iCycles j) ≫
        HomologicalComplex.ιTensorObj (sectionsComplex S P) (sectionsComplex S Q) i j (i + j)
          rfl :=
  (RingTheory.TorProducts.exists_tensorCycles (sectionsComplex S P) (sectionsComplex S Q)
    i j).choose_spec

/-- **The cup product of two global cocycles**: for `z ∈ Zⁱ(Γ(S, P))` and `w ∈ Zʲ(Γ(S, Q))`, the
global cocycle of `Tot(P ⊗ Q)` in degree `i + j` obtained from `z ⊗ w` by the naive cup product
on global sections. -/
def cupCocycle {P Q : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ}
    {i j : ℤ} (z : ModuleCat.of (baseRing S) (baseRing S) ⟶ (sectionsComplex S P).cycles i)
    (w : ModuleCat.of (baseRing S) (baseRing S) ⟶ (sectionsComplex S Q).cycles j) :
    ModuleCat.of (baseRing S) (baseRing S) ⟶
      (sectionsComplex S (HomologicalComplex.mapBifunctor P Q (sheafTensor S.sheaf)
        (ComplexShape.up ℤ))).cycles (i + j) :=
  (λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫ (z ⊗ₘ w) ≫ tensorCycles P Q i j ≫
    HomologicalComplex.cyclesMap
      (Stacks.Cech.SheafTensorPairing.naiveCupProductEval S.sheaf ⊤ P Q) (i + j)

/-- **The cup product of the classes of two global cocycles is the class of their cup
product.** -/
theorem totalCupPairing_globalCycleClass_cupCocycle
    {P Q : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ}
    {i j : ℤ} (z : ModuleCat.of (baseRing S) (baseRing S) ⟶ (sectionsComplex S P).cycles i)
    (w : ModuleCat.of (baseRing S) (baseRing S) ⟶ (sectionsComplex S Q).cycles j) :
    (λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫
        (globalCycleClass z ⊗ₘ globalCycleClass w) ≫ totalCupPairing P Q i j =
      globalCycleClass (cupCocycle z w) :=
  totalCupPairing_globalCycleClass_eq P Q z w (tensorCycles P Q i j) (tensorCycles_iCycles P Q i j)

/-- **The global section underlying the cup product of two global cocycles is the local pure
tensor of their global sections.** -/
theorem cocycleSection_cupCocycle
    {P Q : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ}
    {i j : ℤ} (z : ModuleCat.of (baseRing S) (baseRing S) ⟶ (sectionsComplex S P).cycles i)
    (w : ModuleCat.of (baseRing S) (baseRing S) ⟶ (sectionsComplex S Q).cycles j) :
    cocycleSection (cupCocycle z w) =
      AlgebraicGeometry.RingedSite.tensorComplexSection (spaceSite S) i j (i + j) rfl
        (cocycleSection z) (cocycleSection w) := by
  let x : ((sectionsComplex S P).cycles i ⊗ (sectionsComplex S Q).cycles j :
      ModuleCat.{u} (baseRing S)) :=
    z.hom (1 : baseRing S) ⊗ₜ[baseRing S] w.hom (1 : baseRing S)
  have e0 : cocycleSection (cupCocycle z w) =
      ((HomologicalComplex.cyclesMap
          (Stacks.Cech.SheafTensorPairing.naiveCupProductEval S.sheaf ⊤ P Q) (i + j) ≫
        (sectionsComplex S (HomologicalComplex.mapBifunctor P Q (sheafTensor S.sheaf)
          (ComplexShape.up ℤ))).iCycles (i + j)).hom) ((tensorCycles P Q i j).hom x) := rfl
  have e1 := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i
    (Stacks.Cech.SheafTensorPairing.naiveCupProductEval S.sheaf ⊤ P Q) (i + j))
    ((tensorCycles P Q i j).hom x)
  have e2 := ConcreteCategory.congr_hom (tensorCycles_iCycles P Q i j) x
  refine e0.trans (e1.trans ?_)
  refine (congrArg ((Stacks.Cech.SheafTensorPairing.naiveCupProductEval S.sheaf ⊤ P Q).f
    (i + j)).hom e2).trans ?_
  exact naiveCupProductEval_f_ι_tmul P Q i j (i + j) rfl _ _

/-- **The cup product of the classes of two global cocycles, elementwise**: it is the class of
any global cocycle whose underlying global section is the local pure tensor of theirs. -/
theorem cupClass_globalCycleClass
    {P Q : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ}
    {i j n : ℤ} (h : i + j = n)
    (z : ModuleCat.of (baseRing S) (baseRing S) ⟶ (sectionsComplex S P).cycles i)
    (w : ModuleCat.of (baseRing S) (baseRing S) ⟶ (sectionsComplex S Q).cycles j)
    (ζ : ModuleCat.of (baseRing S) (baseRing S) ⟶
      (sectionsComplex S (HomologicalComplex.mapBifunctor P Q (sheafTensor S.sheaf)
        (ComplexShape.up ℤ))).cycles n)
    (hζ : cocycleSection ζ = AlgebraicGeometry.RingedSite.tensorComplexSection (spaceSite S)
      i j n h (cocycleSection z) (cocycleSection w)) :
    cupClass P Q h ((globalCycleClass z).hom (1 : baseRing S))
        ((globalCycleClass w).hom (1 : baseRing S)) =
      (globalCycleClass ζ).hom (1 : baseRing S) := by
  subst h
  obtain rfl : ζ = cupCocycle z w := cocycle_ext (hζ.trans (cocycleSection_cupCocycle z w).symm)
  have e := ConcreteCategory.congr_hom (totalCupPairing_globalCycleClass_cupCocycle z w)
    (1 : baseRing S)
  rw [leftUnitor_inv_tensorHom_comp_apply_one] at e
  simp only [cupClass, cohomologyCast_rfl, ModuleCat.hom_id]
  exact e

/-- The map induced by a chain map on the class of a global cocycle, elementwise. -/
theorem cohomologyMap_globalCycleClass
    {K K' : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ} (f : K ⟶ K')
    {i : ℤ} (z : ModuleCat.of (baseRing S) (baseRing S) ⟶ (sectionsComplex S K).cycles i)
    (z' : ModuleCat.of (baseRing S) (baseRing S) ⟶ (sectionsComplex S K').cycles i)
    (hz' : cocycleSection z' = (f.f i).val.app (op ⊤) (cocycleSection z)) :
    (cohomologyMap f i).hom ((globalCycleClass z).hom (1 : baseRing S)) =
      (globalCycleClass z').hom (1 : baseRing S) := by
  have hz : z' = z ≫ HomologicalComplex.cyclesMap
      (((globalSections S).mapHomologicalComplex (ComplexShape.up ℤ)).map f) i := by
    refine cocycle_ext (hz'.trans ?_)
    exact (ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i
      (((globalSections S).mapHomologicalComplex (ComplexShape.up ℤ)).map f) i)
        (z.hom (1 : baseRing S))).symm
  subst hz
  exact ConcreteCategory.congr_hom (globalCycleClass_map z f) (1 : baseRing S)

/-- The cup product of the classes of two global cocycles is the class of a global cocycle whose
underlying global section is the local pure tensor of theirs, in any target degree. -/
theorem exists_cupClass_globalCycleClass
    {P Q : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ}
    {i j n : ℤ} (h : i + j = n)
    (z : ModuleCat.of (baseRing S) (baseRing S) ⟶ (sectionsComplex S P).cycles i)
    (w : ModuleCat.of (baseRing S) (baseRing S) ⟶ (sectionsComplex S Q).cycles j) :
    ∃ ζ : ModuleCat.of (baseRing S) (baseRing S) ⟶
        (sectionsComplex S (HomologicalComplex.mapBifunctor P Q (sheafTensor S.sheaf)
          (ComplexShape.up ℤ))).cycles n,
      cocycleSection ζ = AlgebraicGeometry.RingedSite.tensorComplexSection (spaceSite S)
        i j n h (cocycleSection z) (cocycleSection w) ∧
      cupClass P Q h ((globalCycleClass z).hom (1 : baseRing S))
          ((globalCycleClass w).hom (1 : baseRing S)) =
        (globalCycleClass ζ).hom (1 : baseRing S) := by
  subst h
  exact ⟨cupCocycle z w, cocycleSection_cupCocycle z w,
    cupClass_globalCycleClass rfl z w _ (cocycleSection_cupCocycle z w)⟩

/-! ### The reduction to bounded below complexes of flasque modules -/

/-- A Godement resolution of a bounded below complex: a quasi-isomorphism onto a bounded below
complex of flasque modules which is a homotopy equivalence on every stalk (Tag 0FKT). -/
structure GodementData (K : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ)
    where
  /-- The resolution. -/
  obj : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ
  /-- The quasi-isomorphism onto it. -/
  map : K ⟶ obj
  /-- The map is a quasi-isomorphism. -/
  quasiIso : QuasiIso map
  /-- The resolution is bounded below. -/
  boundedBelow : ∃ n : ℤ, obj.IsStrictlyGE n
  /-- The terms of the resolution are flasque. -/
  flasque : ∀ i : ℤ, TopCat.Sheaf.IsFlasque
    ((SheafOfModules.toSheaf (ringSheaf.{u, u, u} S.sheaf)).obj (obj.X i))
  /-- The map is a homotopy equivalence on every stalk. -/
  stalk : ∀ y : S.carrier, ∃ e : HomotopyEquiv
      (AlgebraicGeometry.SheafOfModules.stalkComplex S.sheaf y K)
      (AlgebraicGeometry.SheafOfModules.stalkComplex S.sheaf y obj),
    e.hom = Stacks.Cohomology.FlasqueReduction.stalkComplexMap S.sheaf y map

/-- Every bounded below complex has a Godement resolution. -/
theorem nonempty_godementData
    (K : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ)
    (hK : ∃ n : ℤ, K.IsStrictlyGE n) : Nonempty (GodementData K) := by
  obtain ⟨K₁, a, haqi, hKge, hKfl, hKst⟩ :=
    GodementResolution.exists_quasiIso_boundedBelow_isFlasque_isHomotopyEquiv_stalk_godement
      S K hK
  exact ⟨⟨K₁, a, haqi, hKge, hKfl, fun y => by obtain ⟨e, he⟩ := hKst y; exact ⟨e, he⟩⟩⟩

/-- A quasi-isomorphism induces an isomorphism on the cohomology of derived global sections. -/
theorem isIso_cohomologyMap_of_quasiIso
    {K K' : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ} (f : K ⟶ K')
    (hf : QuasiIso f) (n : ℤ) : IsIso (cohomologyMap f n) := by
  have h1 : IsIso (DerivedCategory.Q.map f) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (φ := f)).2 hf
  exact ((DerivedCategory.homologyFunctor _ n).mapIso ((baseSections S).mapIso
    (@asIso _ _ _ _ (DerivedCategory.Q.map f) h1))).isIso_hom

/-- The map induced by a quasi-isomorphism on the cohomology of derived global sections is
injective. -/
theorem cohomologyMap_injective_of_quasiIso
    {K K' : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ} (f : K ⟶ K')
    (hf : QuasiIso f) (n : ℤ) : Function.Injective (cohomologyMap f n).hom := by
  have := isIso_cohomologyMap_of_quasiIso f hf n
  exact (ConcreteCategory.bijective_of_isIso (cohomologyMap f n)).1

/-- On a bounded below complex of flasque modules every class is the class of a global cocycle. -/
private theorem exists_globalCycleClass_one_eq_of_isFlasque
    (K : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ)
    (hK : ∃ n : ℤ, K.IsStrictlyGE n)
    (hfl : ∀ n : ℤ, TopCat.Sheaf.IsFlasque
      ((SheafOfModules.toSheaf (ringSheaf.{u, u, u} S.sheaf)).obj (K.X n)))
    {i : ℤ} (x : cohomologyModule (DerivedCategory.Q.obj K) i) :
    ∃ z : ModuleCat.of (baseRing S) (baseRing S) ⟶ (sectionsComplex S K).cycles i,
      (globalCycleClass z).hom (1 : baseRing S) = x := by
  obtain ⟨z, hz⟩ := exists_globalCycleClass_eq_of_isFlasque K hK hfl i
    (ModuleCat.ofHom (LinearMap.toSpanSingleton (baseRing S) _ x))
  exact ⟨z, by rw [hz]; simp⟩

/-- On a Godement resolution every class becomes the class of a global cocycle. -/
theorem GodementData.exists_globalCycleClass
    {K : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ}
    (G : GodementData K) {i : ℤ} (x : cohomologyModule (DerivedCategory.Q.obj K) i) :
    ∃ z : ModuleCat.of (baseRing S) (baseRing S) ⟶ (sectionsComplex S G.obj).cycles i,
      (cohomologyMap G.map i).hom x = (globalCycleClass z).hom (1 : baseRing S) := by
  obtain ⟨z, hz⟩ := exists_globalCycleClass_one_eq_of_isFlasque G.obj G.boundedBelow G.flasque
    ((cohomologyMap G.map i).hom x)
  exact ⟨z, hz.symm⟩

/-- The map of total tensor complexes induced by two Godement resolutions is a quasi-isomorphism,
and its stalks are homotopy equivalences. -/
theorem GodementData.quasiIso_mapBifunctorMap
    {K L : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ}
    {K₁ L₁ : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ}
    (a : K ⟶ K₁) (b : L ⟶ L₁)
    (ha : ∀ y : S.carrier, ∃ e : HomotopyEquiv
      (AlgebraicGeometry.SheafOfModules.stalkComplex S.sheaf y K)
      (AlgebraicGeometry.SheafOfModules.stalkComplex S.sheaf y K₁),
      e.hom = Stacks.Cohomology.FlasqueReduction.stalkComplexMap S.sheaf y a)
    (hb : ∀ y : S.carrier, ∃ e : HomotopyEquiv
      (AlgebraicGeometry.SheafOfModules.stalkComplex S.sheaf y L)
      (AlgebraicGeometry.SheafOfModules.stalkComplex S.sheaf y L₁),
      e.hom = Stacks.Cohomology.FlasqueReduction.stalkComplexMap S.sheaf y b) :
    QuasiIso (HomologicalComplex.mapBifunctorMap a b (sheafTensor S.sheaf) (ComplexShape.up ℤ)) :=
  FlasqueReduction.quasiIso_mapBifunctorMap_sheafTensor_of_forall_stalk_homotopyEquiv
    S.sheaf a b ha hb

/-- The maps induced by chain maps compose. -/
theorem cohomologyMap_comp_apply
    {K K' K'' : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ}
    (f : K ⟶ K') (g : K' ⟶ K'') (n : ℤ) (x : cohomologyModule (DerivedCategory.Q.obj K) n) :
    (cohomologyMap g n).hom ((cohomologyMap f n).hom x) = (cohomologyMap (f ≫ g) n).hom x := by
  simp only [cohomologyMap, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

/-- Two ways of pushing a class along a commuting square of chain maps agree. -/
private theorem cohomologyMap_comp_comm_apply
    {K K₁ K₂ K₃ : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ}
    {φ : K ⟶ K₁} {F : K₁ ⟶ K₃} {G : K ⟶ K₂} {φ' : K₂ ⟶ K₃} (hφ : φ ≫ F = G ≫ φ') (n : ℤ)
    (x : cohomologyModule (DerivedCategory.Q.obj K) n) :
    (cohomologyMap F n).hom ((cohomologyMap φ n).hom x) =
      (cohomologyMap φ' n).hom ((cohomologyMap G n).hom x) := by
  rw [cohomologyMap_comp_apply, hφ, ← cohomologyMap_comp_apply]

/-! ### Associativity -/

/-- The left-bracketed cup product of three classes of global cocycles, pushed along a chain map,
is the class of any global cocycle whose section is the image of the iterated local pure tensor. -/
theorem cohomologyMap_cupClass_cupClass_globalCycleClass
    {K L N T : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ}
    (f : HomologicalComplex.mapBifunctor
        (HomologicalComplex.mapBifunctor K L (sheafTensor S.sheaf) (ComplexShape.up ℤ)) N
        (sheafTensor S.sheaf) (ComplexShape.up ℤ) ⟶ T)
    {i j k n : ℤ} (h : i + j + k = n)
    (z : ModuleCat.of (baseRing S) (baseRing S) ⟶ (sectionsComplex S K).cycles i)
    (w : ModuleCat.of (baseRing S) (baseRing S) ⟶ (sectionsComplex S L).cycles j)
    (v : ModuleCat.of (baseRing S) (baseRing S) ⟶ (sectionsComplex S N).cycles k)
    (ζ : ModuleCat.of (baseRing S) (baseRing S) ⟶ (sectionsComplex S T).cycles n)
    (hζ : cocycleSection ζ = (f.f n).val.app (op ⊤)
      (AlgebraicGeometry.RingedSite.tensorComplexSection (spaceSite S) (i + j) k n h
        (AlgebraicGeometry.RingedSite.tensorComplexSection (spaceSite S) i j (i + j) rfl
          (cocycleSection z) (cocycleSection w)) (cocycleSection v))) :
    (cohomologyMap f n).hom
        (cupClass (HomologicalComplex.mapBifunctor K L (sheafTensor S.sheaf) (ComplexShape.up ℤ))
          N h (cupClass K L rfl ((globalCycleClass z).hom (1 : baseRing S))
            ((globalCycleClass w).hom (1 : baseRing S)))
          ((globalCycleClass v).hom (1 : baseRing S))) =
      (globalCycleClass ζ).hom (1 : baseRing S) := by
  subst h
  rw [cupClass_globalCycleClass rfl z w (cupCocycle z w) (cocycleSection_cupCocycle z w),
    cupClass_globalCycleClass rfl (cupCocycle z w) v (cupCocycle (cupCocycle z w) v)
      (cocycleSection_cupCocycle _ _)]
  refine cohomologyMap_globalCycleClass f _ ζ ?_
  rw [hζ, cocycleSection_cupCocycle, cocycleSection_cupCocycle]

/-- The right-bracketed cup product of three classes of global cocycles is the class of any global
cocycle whose section is the iterated local pure tensor. -/
theorem cupClass_cupClass_globalCycleClass
    {K L N : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ}
    {i j k n : ℤ} (h' : i + (j + k) = n)
    (z : ModuleCat.of (baseRing S) (baseRing S) ⟶ (sectionsComplex S K).cycles i)
    (w : ModuleCat.of (baseRing S) (baseRing S) ⟶ (sectionsComplex S L).cycles j)
    (v : ModuleCat.of (baseRing S) (baseRing S) ⟶ (sectionsComplex S N).cycles k)
    (ζ : ModuleCat.of (baseRing S) (baseRing S) ⟶ (sectionsComplex S
      (HomologicalComplex.mapBifunctor K
        (HomologicalComplex.mapBifunctor L N (sheafTensor S.sheaf) (ComplexShape.up ℤ))
        (sheafTensor S.sheaf) (ComplexShape.up ℤ))).cycles n)
    (hζ : cocycleSection ζ =
      AlgebraicGeometry.RingedSite.tensorComplexSection (spaceSite S) i (j + k) n h'
        (cocycleSection z)
        (AlgebraicGeometry.RingedSite.tensorComplexSection (spaceSite S) j k (j + k) rfl
          (cocycleSection w) (cocycleSection v))) :
    cupClass K (HomologicalComplex.mapBifunctor L N (sheafTensor S.sheaf) (ComplexShape.up ℤ))
        h' ((globalCycleClass z).hom (1 : baseRing S))
        (cupClass L N rfl ((globalCycleClass w).hom (1 : baseRing S))
          ((globalCycleClass v).hom (1 : baseRing S))) =
      (globalCycleClass ζ).hom (1 : baseRing S) := by
  rw [cupClass_globalCycleClass rfl w v (cupCocycle w v) (cocycleSection_cupCocycle w v)]
  refine cupClass_globalCycleClass h' z (cupCocycle w v) ζ ?_
  rw [hζ]
  exact congrArg (AlgebraicGeometry.RingedSite.tensorComplexSection (spaceSite S) i (j + k) n h'
    (cocycleSection z)) (cocycleSection_cupCocycle w v).symm

section Assoc

attribute [local instance]
  Stacks.Cohomology.MonoidalComplexesOfModules.cochainComplexMonoidalCategory

/-- The associator `α_` of the monoidal category of complexes of Tag 0FPQ. -/
abbrev monoidalAssociatorHom
    (K L N : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ) :
    (K ⊗ L) ⊗ N ⟶ K ⊗ (L ⊗ N) :=
  (α_ K L N).hom

/-- The associator `α_` of the monoidal category of complexes is natural. -/
theorem monoidalAssociatorHom_naturality
    {K K' L L' N N' : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ}
    (a : K ⟶ K') (b : L ⟶ L') (c : N ⟶ N') :
    ((a ⊗ₘ b) ⊗ₘ c) ≫ monoidalAssociatorHom K' L' N' =
      monoidalAssociatorHom K L N ≫ (a ⊗ₘ (b ⊗ₘ c)) :=
  MonoidalCategory.associator_naturality a b c

end Assoc

/-- **The associator of total tensor complexes**, `Tot(Tot(K ⊗ L) ⊗ N) ⟶ Tot(K ⊗ Tot(L ⊗ N))`:
the associator `α_` of the symmetric monoidal category of complexes of `𝒪_S`-modules of
Tag 0FPQ (`Stacks.Cohomology.MonoidalComplexesOfModules.cochainComplexMonoidalCategory`), whose
tensor product is the total tensor complex on the nose, written at the spelling of iterated
`HomologicalComplex.mapBifunctor`. -/
def tensorAssociator (K L N : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ) :
    HomologicalComplex.mapBifunctor
        (HomologicalComplex.mapBifunctor K L (sheafTensor S.sheaf) (ComplexShape.up ℤ)) N
        (sheafTensor S.sheaf) (ComplexShape.up ℤ) ⟶
      HomologicalComplex.mapBifunctor K
        (HomologicalComplex.mapBifunctor L N (sheafTensor S.sheaf) (ComplexShape.up ℤ))
        (sheafTensor S.sheaf) (ComplexShape.up ℤ) :=
  monoidalAssociatorHom K L N

/-- The associator of total tensor complexes is natural. -/
theorem tensorAssociator_naturality
    {K K' L L' N N' : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ}
    (a : K ⟶ K') (b : L ⟶ L') (c : N ⟶ N') :
    tensorAssociator K L N ≫ HomologicalComplex.mapBifunctorMap a
      (HomologicalComplex.mapBifunctorMap b c (sheafTensor S.sheaf) (ComplexShape.up ℤ))
      (sheafTensor S.sheaf) (ComplexShape.up ℤ) =
      HomologicalComplex.mapBifunctorMap
        (HomologicalComplex.mapBifunctorMap a b (sheafTensor S.sheaf) (ComplexShape.up ℤ))
        c (sheafTensor S.sheaf) (ComplexShape.up ℤ) ≫ tensorAssociator K' L' N' :=
  (monoidalAssociatorHom_naturality a b c).symm

/-- The associator of total tensor complexes reassociates an iterated local pure tensor. -/
theorem tensorAssociator_tensorComplexSection
    (K L N : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ)
    {i j k n : ℤ} (h : i + j + k = n) (h' : i + (j + k) = n)
    (a : (K.X i).val.obj (op ⊤)) (b : (L.X j).val.obj (op ⊤)) (c : (N.X k).val.obj (op ⊤)) :
    ((tensorAssociator K L N).f n).val.app (op ⊤)
        (AlgebraicGeometry.RingedSite.tensorComplexSection (spaceSite S) (i + j) k n h
          (AlgebraicGeometry.RingedSite.tensorComplexSection (spaceSite S) i j (i + j) rfl a b)
          c) =
      AlgebraicGeometry.RingedSite.tensorComplexSection (spaceSite S) i (j + k) n h' a
        (AlgebraicGeometry.RingedSite.tensorComplexSection (spaceSite S) j k (j + k) rfl b c) :=
  AlgebraicGeometry.RingedSite.associator_tensorComplexSection (spaceSite S) K L N ⊤ i j k n h h'
    a b c

/-- Transport of the left-bracketed side of associativity along three chain maps. -/
theorem cohomologyMap_tensorAssociator_cupClass_cupClass
    {K K' L L' N N' : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ}
    (a : K ⟶ K') (b : L ⟶ L') (c : N ⟶ N') {i j k n : ℤ} (h : i + j + k = n)
    (ξ : cohomologyModule (DerivedCategory.Q.obj K) i)
    (η : cohomologyModule (DerivedCategory.Q.obj L) j)
    (ζ : cohomologyModule (DerivedCategory.Q.obj N) k) :
    (cohomologyMap (HomologicalComplex.mapBifunctorMap a
        (HomologicalComplex.mapBifunctorMap b c (sheafTensor S.sheaf) (ComplexShape.up ℤ))
        (sheafTensor S.sheaf) (ComplexShape.up ℤ)) n).hom
      ((cohomologyMap (tensorAssociator K L N) n).hom
        (cupClass (HomologicalComplex.mapBifunctor K L (sheafTensor S.sheaf) (ComplexShape.up ℤ))
          N h (cupClass K L rfl ξ η) ζ)) =
      (cohomologyMap (tensorAssociator K' L' N') n).hom
        (cupClass (HomologicalComplex.mapBifunctor K' L' (sheafTensor S.sheaf) (ComplexShape.up ℤ))
          N' h (cupClass K' L' rfl ((cohomologyMap a i).hom ξ) ((cohomologyMap b j).hom η))
          ((cohomologyMap c k).hom ζ)) := by
  refine (cohomologyMap_comp_comm_apply (tensorAssociator_naturality a b c) n _).trans
    (congrArg (cohomologyMap (tensorAssociator K' L' N') n).hom ?_)
  exact (cupClass_naturality (HomologicalComplex.mapBifunctorMap a b (sheafTensor S.sheaf)
    (ComplexShape.up ℤ)) c h (cupClass K L rfl ξ η) ζ).trans
    (congrArg (fun t => cupClass _ N' h t ((cohomologyMap c k).hom ζ))
      (cupClass_naturality a b rfl ξ η))

/-- Transport of the right-bracketed side of associativity along three chain maps. -/
theorem cohomologyMap_cupClass_cupClass
    {K K' L L' N N' : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ}
    (a : K ⟶ K') (b : L ⟶ L') (c : N ⟶ N') {i j k n : ℤ} (h' : i + (j + k) = n)
    (ξ : cohomologyModule (DerivedCategory.Q.obj K) i)
    (η : cohomologyModule (DerivedCategory.Q.obj L) j)
    (ζ : cohomologyModule (DerivedCategory.Q.obj N) k) :
    (cohomologyMap (HomologicalComplex.mapBifunctorMap a
        (HomologicalComplex.mapBifunctorMap b c (sheafTensor S.sheaf) (ComplexShape.up ℤ))
        (sheafTensor S.sheaf) (ComplexShape.up ℤ)) n).hom
      (cupClass K (HomologicalComplex.mapBifunctor L N (sheafTensor S.sheaf) (ComplexShape.up ℤ))
        h' ξ (cupClass L N rfl η ζ)) =
      cupClass K' (HomologicalComplex.mapBifunctor L' N' (sheafTensor S.sheaf) (ComplexShape.up ℤ))
        h' ((cohomologyMap a i).hom ξ)
        (cupClass L' N' rfl ((cohomologyMap b j).hom η) ((cohomologyMap c k).hom ζ)) := by
  rw [cupClass_naturality a (HomologicalComplex.mapBifunctorMap b c (sheafTensor S.sheaf)
      (ComplexShape.up ℤ)) h', cupClass_naturality b c rfl]

/-- Associativity on bounded below complexes of flasque modules, on classes of global cocycles. -/
theorem cupClass_assoc_globalCycleClass
    {K L N : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ}
    {i j k n : ℤ} (h : i + j + k = n) (h' : i + (j + k) = n)
    (z : ModuleCat.of (baseRing S) (baseRing S) ⟶ (sectionsComplex S K).cycles i)
    (w : ModuleCat.of (baseRing S) (baseRing S) ⟶ (sectionsComplex S L).cycles j)
    (v : ModuleCat.of (baseRing S) (baseRing S) ⟶ (sectionsComplex S N).cycles k) :
    (cohomologyMap (tensorAssociator K L N) n).hom
        (cupClass (HomologicalComplex.mapBifunctor K L (sheafTensor S.sheaf) (ComplexShape.up ℤ))
          N h (cupClass K L rfl ((globalCycleClass z).hom (1 : baseRing S))
            ((globalCycleClass w).hom (1 : baseRing S)))
          ((globalCycleClass v).hom (1 : baseRing S))) =
      cupClass K (HomologicalComplex.mapBifunctor L N (sheafTensor S.sheaf) (ComplexShape.up ℤ))
        h' ((globalCycleClass z).hom (1 : baseRing S))
        (cupClass L N rfl ((globalCycleClass w).hom (1 : baseRing S))
          ((globalCycleClass v).hom (1 : baseRing S))) := by
  obtain ⟨ζR, hsR, -⟩ := exists_cupClass_globalCycleClass h' z (cupCocycle w v)
  have hsR' : cocycleSection ζR =
      AlgebraicGeometry.RingedSite.tensorComplexSection (spaceSite S) i (j + k) n h'
        (cocycleSection z)
        (AlgebraicGeometry.RingedSite.tensorComplexSection (spaceSite S) j k (j + k) rfl
          (cocycleSection w) (cocycleSection v)) :=
    hsR.trans (congrArg (AlgebraicGeometry.RingedSite.tensorComplexSection (spaceSite S) i
      (j + k) n h' (cocycleSection z)) (cocycleSection_cupCocycle w v))
  refine (cohomologyMap_cupClass_cupClass_globalCycleClass (tensorAssociator K L N) h z w v ζR
    ?_).trans (cupClass_cupClass_globalCycleClass h' z w v ζR hsR').symm
  exact hsR'.trans (tensorAssociator_tensorComplexSection K L N h h' _ _ _).symm

/-- Associativity on bounded below complexes of flasque modules. -/
theorem cupClass_assoc_of_isFlasque
    {K L N : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ}
    (hK : ∃ n : ℤ, K.IsStrictlyGE n) (hL : ∃ n : ℤ, L.IsStrictlyGE n)
    (hN : ∃ n : ℤ, N.IsStrictlyGE n)
    (hKfl : ∀ n : ℤ, TopCat.Sheaf.IsFlasque
      ((SheafOfModules.toSheaf (ringSheaf.{u, u, u} S.sheaf)).obj (K.X n)))
    (hLfl : ∀ n : ℤ, TopCat.Sheaf.IsFlasque
      ((SheafOfModules.toSheaf (ringSheaf.{u, u, u} S.sheaf)).obj (L.X n)))
    (hNfl : ∀ n : ℤ, TopCat.Sheaf.IsFlasque
      ((SheafOfModules.toSheaf (ringSheaf.{u, u, u} S.sheaf)).obj (N.X n)))
    {i j k n : ℤ} (h : i + j + k = n) (h' : i + (j + k) = n)
    (ξ : cohomologyModule (DerivedCategory.Q.obj K) i)
    (η : cohomologyModule (DerivedCategory.Q.obj L) j)
    (ζ : cohomologyModule (DerivedCategory.Q.obj N) k) :
    (cohomologyMap (tensorAssociator K L N) n).hom
        (cupClass (HomologicalComplex.mapBifunctor K L (sheafTensor S.sheaf) (ComplexShape.up ℤ))
          N h (cupClass K L rfl ξ η) ζ) =
      cupClass K (HomologicalComplex.mapBifunctor L N (sheafTensor S.sheaf) (ComplexShape.up ℤ))
        h' ξ (cupClass L N rfl η ζ) := by
  obtain ⟨z, hz⟩ := exists_globalCycleClass_one_eq_of_isFlasque K hK hKfl ξ
  obtain ⟨w, hw⟩ := exists_globalCycleClass_one_eq_of_isFlasque L hL hLfl η
  obtain ⟨v, hv⟩ := exists_globalCycleClass_one_eq_of_isFlasque N hN hNfl ζ
  subst hz hw hv
  exact cupClass_assoc_globalCycleClass h h' z w v

/-- **The cup product on total tensor complexes is associative.** For bounded below complexes
`K`, `L`, `N` of `𝒪_S`-modules and classes `ξ ∈ Hⁱ(S, K)`, `η ∈ Hʲ(S, L)`, `ζ ∈ Hᵏ(S, N)`, the
associator `Tot(Tot(K ⊗ L) ⊗ N) ≅ Tot(K ⊗ Tot(L ⊗ N))` of the symmetric monoidal category of
complexes (Tag 0FPQ) carries `(ξ ∪ η) ∪ ζ` to `ξ ∪ (η ∪ ζ)`, in every degree
`n = i + j + k`. -/
theorem cupClass_assoc (K L N : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ)
    (hK : ∃ n : ℤ, K.IsStrictlyGE n) (hL : ∃ n : ℤ, L.IsStrictlyGE n)
    (hN : ∃ n : ℤ, N.IsStrictlyGE n) {i j k n : ℤ} (h : i + j + k = n) (h' : i + (j + k) = n)
    (ξ : cohomologyModule (DerivedCategory.Q.obj K) i)
    (η : cohomologyModule (DerivedCategory.Q.obj L) j)
    (ζ : cohomologyModule (DerivedCategory.Q.obj N) k) :
    (cohomologyMap (tensorAssociator K L N) n).hom
        (cupClass (HomologicalComplex.mapBifunctor K L (sheafTensor S.sheaf) (ComplexShape.up ℤ))
          N h (cupClass K L rfl ξ η) ζ) =
      cupClass K (HomologicalComplex.mapBifunctor L N (sheafTensor S.sheaf) (ComplexShape.up ℤ))
        h' ξ (cupClass L N rfl η ζ) := by
  obtain ⟨Ga⟩ := nonempty_godementData K hK
  obtain ⟨Gb⟩ := nonempty_godementData L hL
  obtain ⟨Gc⟩ := nonempty_godementData N hN
  have hbc := Stacks.Cohomology.FlasqueReduction.exists_stalk_homotopyEquiv_mapBifunctorMap
    S.sheaf Gb.map Gc.map Gb.stalk Gc.stalk
  have hf := GodementData.quasiIso_mapBifunctorMap Ga.map
    (HomologicalComplex.mapBifunctorMap Gb.map Gc.map (sheafTensor S.sheaf) (ComplexShape.up ℤ))
    Ga.stalk hbc
  exact cohomologyMap_injective_of_quasiIso _ hf n
    ((cohomologyMap_tensorAssociator_cupClass_cupClass Ga.map Gb.map Gc.map h ξ η ζ).trans
      ((cupClass_assoc_of_isFlasque Ga.boundedBelow Gb.boundedBelow Gc.boundedBelow Ga.flasque
        Gb.flasque Gc.flasque h h' _ _ _).trans
        (cohomologyMap_cupClass_cupClass Ga.map Gb.map Gc.map h' ξ η ζ).symm))

/-! ### Graded commutativity -/

section Braid

attribute [local instance]
  Stacks.Cohomology.MonoidalComplexesOfModules.cochainComplexMonoidalCategory
  Stacks.Cohomology.MonoidalComplexesOfModules.cochainComplexSymmetricCategory

/-- The commutativity constraint `β_` of the symmetric monoidal category of complexes of
Tag 0FPQ: the Koszul symmetry. -/
abbrev monoidalBraidingHom
    (K L : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ) :
    K ⊗ L ⟶ L ⊗ K :=
  (β_ K L).hom

/-- The commutativity constraint `β_` of the symmetric monoidal category of complexes is
natural. -/
theorem monoidalBraidingHom_naturality
    {K K' L L' : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ}
    (a : K ⟶ K') (b : L ⟶ L') :
    (a ⊗ₘ b) ≫ monoidalBraidingHom K' L' = monoidalBraidingHom K L ≫ (b ⊗ₘ a) :=
  BraidedCategory.braiding_naturality a b

end Braid

/-- **The commutativity constraint of total tensor complexes**, `Tot(K ⊗ L) ⟶ Tot(L ⊗ K)`: the
braiding `β_` of the symmetric monoidal category of complexes of `𝒪_S`-modules of Tag 0FPQ,
which on the summand `Kᵖ ⊗ Lᵠ` is the symmetry of the sheaf tensor product times the Koszul sign
`(-1)^{pq}`, written at the spelling of `HomologicalComplex.mapBifunctor`. -/
def tensorBraiding (K L : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ) :
    HomologicalComplex.mapBifunctor K L (sheafTensor S.sheaf) (ComplexShape.up ℤ) ⟶
      HomologicalComplex.mapBifunctor L K (sheafTensor S.sheaf) (ComplexShape.up ℤ) :=
  monoidalBraidingHom K L

/-- The commutativity constraint of total tensor complexes is natural. -/
theorem tensorBraiding_naturality
    {K K' L L' : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ}
    (a : K ⟶ K') (b : L ⟶ L') :
    tensorBraiding K L ≫ HomologicalComplex.mapBifunctorMap b a (sheafTensor S.sheaf)
        (ComplexShape.up ℤ) =
      HomologicalComplex.mapBifunctorMap a b (sheafTensor S.sheaf) (ComplexShape.up ℤ) ≫
        tensorBraiding K' L' :=
  (monoidalBraidingHom_naturality a b).symm

section BraidSection

attribute [local instance] SheafOfModules.monoidalCategorySheafTensor
  SheafOfModules.symmetricCategorySheafTensor SheafOfModules.monoidalPreadditiveSheafTensor
  SheafOfModules.monoidalClosedSheafTensor
  SheafOfModules.preservesColimit_tensorRight_sheafTensor

/-- An integer sign multiple of a morphism of sheaves of modules acts on sections by the
sign. -/
private theorem units_smul_val_app {M N : SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)}
    (e : ℤˣ) (φ : M ⟶ N) (U : (Opens S.carrier)ᵒᵖ) (x : M.val.obj U) :
    (e • φ).val.app U x = e • φ.val.app U x := by
  rw [Units.smul_def, Units.smul_def]
  exact map_zsmul (AddMonoidHom.mk' (fun ψ : M ⟶ N ↦ ψ.val.app U x) fun _ _ ↦ rfl) (e : ℤ) φ

/-- **The commutativity constraint of total tensor complexes on a local pure tensor**:
`s ⊗ t ↦ (-1)^{ij} t ⊗ s` for `s` of degree `i` and `t` of degree `j`. -/
theorem tensorBraiding_tensorComplexSection
    (K L : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ)
    {i j n : ℤ} (h : i + j = n) (h' : j + i = n)
    (a : (K.X i).val.obj (op ⊤)) (b : (L.X j).val.obj (op ⊤)) :
    ((tensorBraiding K L).f n).val.app (op ⊤)
        (AlgebraicGeometry.RingedSite.tensorComplexSection (spaceSite S) i j n h a b) =
      (i * j).negOnePow •
        AlgebraicGeometry.RingedSite.tensorComplexSection (spaceSite S) j i n h' b a := by
  have e := Stacks.Cohomology.MonoidalComplexesOfModules.ιTensorObj_braiding_hom_f S.sheaf K L
    i j n h
  have e1 := congrArg (fun t => t.val.app (op ⊤)
    (AlgebraicGeometry.RingedSite.moduleTensorSection (spaceSite S) (op ⊤) (K.X i) (L.X j) a b))
    e
  refine e1.trans ((units_smul_val_app _ _ _ _).trans ?_)
  refine congrArg (((i * j).negOnePow : ℤˣ) • ·) ?_
  have e2 := Stacks.SheafOfModules.Tensor.braiding_hom_app_sheafifyUnit_tmul S.sheaf (K.X i)
    (L.X j) (op ⊤) a b
  exact congrArg (fun x => ((HomologicalComplex.ιTensorObj L K j i n
    (by simpa [add_comm] using h)).val.app (op ⊤)) x) e2

end BraidSection

/-- The global section underlying a sign multiple of a global cocycle. -/
theorem cocycleSection_units_smul
    {K : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ} {i : ℤ} (e : ℤˣ)
    (z : ModuleCat.of (baseRing S) (baseRing S) ⟶ (sectionsComplex S K).cycles i) :
    cocycleSection (e • z) = e • cocycleSection z := by
  have h1 : (e • z) ≫ (sectionsComplex S K).iCycles i =
      ((e : ℤ) • (z ≫ (sectionsComplex S K).iCycles i)) := by
    rw [Linear.units_smul_comp, Units.smul_def]
  change ((e • z) ≫ (sectionsComplex S K).iCycles i).hom (1 : baseRing S) = _
  rw [h1, ModuleCat.hom_zsmul, LinearMap.smul_apply, ← Units.smul_def]
  rfl

/-- The class of a sign multiple of a global cocycle, elementwise. -/
theorem globalCycleClass_units_smul_one
    {K : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ} {i : ℤ} (e : ℤˣ)
    (z : ModuleCat.of (baseRing S) (baseRing S) ⟶ (sectionsComplex S K).cycles i) :
    (globalCycleClass (e • z)).hom (1 : baseRing S) =
      (e : ℤ) • (globalCycleClass z).hom (1 : baseRing S) := by
  rw [globalCycleClass_units_smul, Units.smul_def, ModuleCat.hom_zsmul, LinearMap.smul_apply]

/-- Graded commutativity on classes of global cocycles. -/
theorem cupClass_comm_globalCycleClass
    {K L : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ}
    {i j n : ℤ} (h : i + j = n) (h' : j + i = n)
    (z : ModuleCat.of (baseRing S) (baseRing S) ⟶ (sectionsComplex S K).cycles i)
    (w : ModuleCat.of (baseRing S) (baseRing S) ⟶ (sectionsComplex S L).cycles j) :
    (cohomologyMap (tensorBraiding K L) n).hom
        (cupClass K L h ((globalCycleClass z).hom (1 : baseRing S))
          ((globalCycleClass w).hom (1 : baseRing S))) =
      ((i * j).negOnePow : ℤ) • cupClass L K h' ((globalCycleClass w).hom (1 : baseRing S))
        ((globalCycleClass z).hom (1 : baseRing S)) := by
  subst h
  obtain ⟨ζ', hs', e'⟩ := exists_cupClass_globalCycleClass h' w z
  rw [cupClass_globalCycleClass rfl z w (cupCocycle z w) (cocycleSection_cupCocycle z w), e']
  refine (cohomologyMap_globalCycleClass (tensorBraiding K L) (cupCocycle z w)
    ((i * j).negOnePow • ζ') ?_).trans ?_
  · exact (cocycleSection_units_smul _ ζ').trans ((congrArg (fun x => (i * j).negOnePow • x)
      hs').trans ((tensorBraiding_tensorComplexSection K L rfl h' (cocycleSection z)
        (cocycleSection w)).symm.trans (congrArg (fun x =>
          ((tensorBraiding K L).f (i + j)).val.app (op ⊤) x)
          (cocycleSection_cupCocycle z w).symm)))
  · exact globalCycleClass_units_smul_one _ ζ'

/-- Transport of the left side of graded commutativity along two chain maps. -/
theorem cohomologyMap_tensorBraiding_cupClass
    {K K' L L' : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ}
    (a : K ⟶ K') (b : L ⟶ L') {i j n : ℤ} (h : i + j = n)
    (ξ : cohomologyModule (DerivedCategory.Q.obj K) i)
    (η : cohomologyModule (DerivedCategory.Q.obj L) j) :
    (cohomologyMap (HomologicalComplex.mapBifunctorMap b a (sheafTensor S.sheaf)
        (ComplexShape.up ℤ)) n).hom ((cohomologyMap (tensorBraiding K L) n).hom
          (cupClass K L h ξ η)) =
      (cohomologyMap (tensorBraiding K' L') n).hom
        (cupClass K' L' h ((cohomologyMap a i).hom ξ) ((cohomologyMap b j).hom η)) := by
  rw [cohomologyMap_comp_comm_apply (tensorBraiding_naturality a b), cupClass_naturality a b h]

/-- Graded commutativity on bounded below complexes of flasque modules. -/
theorem cupClass_comm_of_isFlasque
    {K L : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ}
    (hK : ∃ n : ℤ, K.IsStrictlyGE n) (hL : ∃ n : ℤ, L.IsStrictlyGE n)
    (hKfl : ∀ n : ℤ, TopCat.Sheaf.IsFlasque
      ((SheafOfModules.toSheaf (ringSheaf.{u, u, u} S.sheaf)).obj (K.X n)))
    (hLfl : ∀ n : ℤ, TopCat.Sheaf.IsFlasque
      ((SheafOfModules.toSheaf (ringSheaf.{u, u, u} S.sheaf)).obj (L.X n)))
    {i j n : ℤ} (h : i + j = n) (h' : j + i = n)
    (ξ : cohomologyModule (DerivedCategory.Q.obj K) i)
    (η : cohomologyModule (DerivedCategory.Q.obj L) j) :
    (cohomologyMap (tensorBraiding K L) n).hom (cupClass K L h ξ η) =
      ((i * j).negOnePow : ℤ) • cupClass L K h' η ξ := by
  obtain ⟨z, rfl⟩ := exists_globalCycleClass_one_eq_of_isFlasque K hK hKfl ξ
  obtain ⟨w, rfl⟩ := exists_globalCycleClass_one_eq_of_isFlasque L hL hLfl η
  exact cupClass_comm_globalCycleClass h h' z w

/-- **The cup product on total tensor complexes is graded commutative.** For bounded below
complexes `K`, `L` of `𝒪_S`-modules and classes `ξ ∈ Hⁱ(S, K)`, `η ∈ Hʲ(S, L)`, the
commutativity constraint `Tot(K ⊗ L) ≅ Tot(L ⊗ K)` of the symmetric monoidal category of
complexes (Tag 0FPQ), the Koszul symmetry, carries `ξ ∪ η` to `(-1)^{ij} η ∪ ξ`. -/
theorem cupClass_comm (K L : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ)
    (hK : ∃ n : ℤ, K.IsStrictlyGE n) (hL : ∃ n : ℤ, L.IsStrictlyGE n) {i j n : ℤ}
    (h : i + j = n) (h' : j + i = n)
    (ξ : cohomologyModule (DerivedCategory.Q.obj K) i)
    (η : cohomologyModule (DerivedCategory.Q.obj L) j) :
    (cohomologyMap (tensorBraiding K L) n).hom (cupClass K L h ξ η) =
      ((i * j).negOnePow : ℤ) • cupClass L K h' η ξ := by
  obtain ⟨Ga⟩ := nonempty_godementData K hK
  obtain ⟨Gb⟩ := nonempty_godementData L hL
  have hf := GodementData.quasiIso_mapBifunctorMap Gb.map Ga.map Gb.stalk Ga.stalk
  apply cohomologyMap_injective_of_quasiIso _ hf n
  refine (cohomologyMap_tensorBraiding_cupClass Ga.map Gb.map h ξ η).trans ?_
  refine (cupClass_comm_of_isFlasque Ga.boundedBelow Gb.boundedBelow Ga.flasque Gb.flasque h h'
    _ _).trans ?_
  rw [map_zsmul, cupClass_naturality Gb.map Ga.map h' η ξ]

/-- The degree cast of the image of a cup product under a chain map. -/
theorem cohomologyCast_cohomologyMap_cupClass
    {K L M : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ}
    (f : HomologicalComplex.mapBifunctor K L (sheafTensor S.sheaf) (ComplexShape.up ℤ) ⟶ M)
    {i j n : ℤ} (h : i + j = n)
    (ξ : cohomologyModule (DerivedCategory.Q.obj K) i)
    (η : cohomologyModule (DerivedCategory.Q.obj L) j) :
    (cohomologyCast (DerivedCategory.Q.obj M) h).hom
        ((cohomologyMap f (i + j)).hom (cupClass K L rfl ξ η)) =
      (cohomologyMap f n).hom (cupClass K L h ξ η) := by
  subst h
  rfl

/-! ### The laws for multiplications of complexes -/

/-- The left-bracketed triple product along two chain maps, as the image of the triple product
on total tensor complexes. -/
theorem cohomologyCast_cupClass_left_of_comp
    {K L N P M : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ}
    (f₁ : HomologicalComplex.mapBifunctor K L (sheafTensor S.sheaf) (ComplexShape.up ℤ) ⟶ P)
    (f₂ : HomologicalComplex.mapBifunctor P N (sheafTensor S.sheaf) (ComplexShape.up ℤ) ⟶ M)
    {i j k n : ℤ} (h : i + j + k = n) (ξ : cohomologyModule (DerivedCategory.Q.obj K) i)
    (η : cohomologyModule (DerivedCategory.Q.obj L) j)
    (ζ : cohomologyModule (DerivedCategory.Q.obj N) k) :
    (cohomologyCast (DerivedCategory.Q.obj M) h).hom
        ((cohomologyMap f₂ (i + j + k)).hom
          (cupClass P N rfl ((cohomologyMap f₁ (i + j)).hom (cupClass K L rfl ξ η)) ζ)) =
      (cohomologyMap (HomologicalComplex.mapBifunctorMap f₁ (𝟙 N) (sheafTensor S.sheaf)
          (ComplexShape.up ℤ) ≫ f₂) n).hom
        (cupClass (HomologicalComplex.mapBifunctor K L (sheafTensor S.sheaf) (ComplexShape.up ℤ))
          N h (cupClass K L rfl ξ η) ζ) := by
  subst h
  have e1 := (cupClass_naturality f₁ (𝟙 N) (rfl : i + j + k = i + j + k)
    (cupClass K L rfl ξ η) ζ).trans
      (congrArg (cupClass P N rfl ((cohomologyMap f₁ (i + j)).hom (cupClass K L rfl ξ η)))
        (cohomologyMap_id_apply N k ζ))
  exact (congrArg (cohomologyMap f₂ (i + j + k)).hom e1.symm).trans
    (cohomologyMap_comp_apply _ f₂ (i + j + k) _)

/-- The right-bracketed triple product along two chain maps, as the image of the triple product
on total tensor complexes. -/
theorem cupClass_right_of_comp
    {K L N Q M : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ}
    (f₃ : HomologicalComplex.mapBifunctor L N (sheafTensor S.sheaf) (ComplexShape.up ℤ) ⟶ Q)
    (f₄ : HomologicalComplex.mapBifunctor K Q (sheafTensor S.sheaf) (ComplexShape.up ℤ) ⟶ M)
    {i j k : ℤ} (ξ : cohomologyModule (DerivedCategory.Q.obj K) i)
    (η : cohomologyModule (DerivedCategory.Q.obj L) j)
    (ζ : cohomologyModule (DerivedCategory.Q.obj N) k) :
    (cohomologyMap f₄ (i + (j + k))).hom
        (cupClass K Q rfl ξ ((cohomologyMap f₃ (j + k)).hom (cupClass L N rfl η ζ))) =
      (cohomologyMap (HomologicalComplex.mapBifunctorMap (𝟙 K) f₃ (sheafTensor S.sheaf)
          (ComplexShape.up ℤ) ≫ f₄) (i + (j + k))).hom
        (cupClass K (HomologicalComplex.mapBifunctor L N (sheafTensor S.sheaf) (ComplexShape.up ℤ))
          rfl ξ (cupClass L N rfl η ζ)) := by
  have e1 := (cupClass_naturality (𝟙 K) f₃ (rfl : i + (j + k) = i + (j + k)) ξ
    (cupClass L N rfl η ζ)).trans
      (congrArg (fun t => cupClass K Q rfl t ((cohomologyMap f₃ (j + k)).hom
        (cupClass L N rfl η ζ))) (cohomologyMap_id_apply K i ξ))
  exact (congrArg (cohomologyMap f₄ (i + (j + k))).hom e1.symm).trans
    (cohomologyMap_comp_apply _ f₄ (i + (j + k)) _)

/-- **Associativity of the cup product along multiplications of complexes.** Let
`f₁ : Tot(K ⊗ L) ⟶ P`, `f₂ : Tot(P ⊗ N) ⟶ M`, `f₃ : Tot(L ⊗ N) ⟶ Q`, `f₄ : Tot(K ⊗ Q) ⟶ M` be
chain maps with `f₂ ∘ (f₁ ⊗ 1) = f₄ ∘ (1 ⊗ f₃) ∘ α`, `K`, `L`, `N` bounded below. Then the two
bracketings of the induced triple cup product agree, the left one read in degree `i + (j + k)`. -/
theorem cupClass_assoc_of_comp
    {K L N P Q M : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ}
    (hK : ∃ n : ℤ, K.IsStrictlyGE n) (hL : ∃ n : ℤ, L.IsStrictlyGE n)
    (hN : ∃ n : ℤ, N.IsStrictlyGE n)
    (f₁ : HomologicalComplex.mapBifunctor K L (sheafTensor S.sheaf) (ComplexShape.up ℤ) ⟶ P)
    (f₂ : HomologicalComplex.mapBifunctor P N (sheafTensor S.sheaf) (ComplexShape.up ℤ) ⟶ M)
    (f₃ : HomologicalComplex.mapBifunctor L N (sheafTensor S.sheaf) (ComplexShape.up ℤ) ⟶ Q)
    (f₄ : HomologicalComplex.mapBifunctor K Q (sheafTensor S.sheaf) (ComplexShape.up ℤ) ⟶ M)
    (hf : HomologicalComplex.mapBifunctorMap f₁ (𝟙 N) (sheafTensor S.sheaf) (ComplexShape.up ℤ) ≫
        f₂ = tensorAssociator K L N ≫
          HomologicalComplex.mapBifunctorMap (𝟙 K) f₃ (sheafTensor S.sheaf) (ComplexShape.up ℤ) ≫
            f₄)
    (i j k : ℤ) (ξ : cohomologyModule (DerivedCategory.Q.obj K) i)
    (η : cohomologyModule (DerivedCategory.Q.obj L) j)
    (ζ : cohomologyModule (DerivedCategory.Q.obj N) k) :
    (cohomologyCast (DerivedCategory.Q.obj M) (add_assoc i j k)).hom
        ((cohomologyMap f₂ (i + j + k)).hom
          (cupClass P N rfl ((cohomologyMap f₁ (i + j)).hom (cupClass K L rfl ξ η)) ζ)) =
      (cohomologyMap f₄ (i + (j + k))).hom
        (cupClass K Q rfl ξ ((cohomologyMap f₃ (j + k)).hom (cupClass L N rfl η ζ))) := by
  refine (cohomologyCast_cupClass_left_of_comp f₁ f₂ (add_assoc i j k) ξ η ζ).trans ?_
  refine Eq.trans ?_ (cupClass_right_of_comp f₃ f₄ ξ η ζ).symm
  refine (congrArg (fun t => (cohomologyMap t (i + (j + k))).hom _) hf).trans ?_
  refine (cohomologyMap_comp_apply (tensorAssociator K L N) _ (i + (j + k)) _).symm.trans ?_
  exact congrArg (cohomologyMap _ (i + (j + k))).hom
    (cupClass_assoc K L N hK hL hN (add_assoc i j k) rfl ξ η ζ)

/-- **Graded commutativity of the cup product along multiplications of complexes.** Let
`f : Tot(K ⊗ L) ⟶ M` and `f' : Tot(L ⊗ K) ⟶ M` be chain maps with `f' ∘ β = f` for the Koszul
symmetry `β` of Tag 0FPQ, `K`, `L` bounded below. Then `f(ξ ∪ η) = (-1)^{ij} f'(η ∪ ξ)`, the
right-hand side read in degree `i + j`. -/
theorem cupClass_comm_of_comp
    {K L M : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ}
    (hK : ∃ n : ℤ, K.IsStrictlyGE n) (hL : ∃ n : ℤ, L.IsStrictlyGE n)
    (f : HomologicalComplex.mapBifunctor K L (sheafTensor S.sheaf) (ComplexShape.up ℤ) ⟶ M)
    (f' : HomologicalComplex.mapBifunctor L K (sheafTensor S.sheaf) (ComplexShape.up ℤ) ⟶ M)
    (hf : tensorBraiding K L ≫ f' = f) (i j : ℤ)
    (ξ : cohomologyModule (DerivedCategory.Q.obj K) i)
    (η : cohomologyModule (DerivedCategory.Q.obj L) j) :
    (cohomologyMap f (i + j)).hom (cupClass K L rfl ξ η) =
      ((i * j).negOnePow : ℤ) • (cohomologyCast (DerivedCategory.Q.obj M) (add_comm j i)).hom
        ((cohomologyMap f' (j + i)).hom (cupClass L K rfl η ξ)) := by
  subst hf
  refine (cohomologyMap_comp_apply (tensorBraiding K L) f' (i + j) _).symm.trans ?_
  refine (congrArg (cohomologyMap f' (i + j)).hom
    (cupClass_comm K L hK hL rfl (add_comm j i) ξ η)).trans ?_
  rw [map_zsmul, cohomologyCast_cohomologyMap_cupClass f' (add_comm j i) η ξ]

end Stacks.Cohomology.DerivedGlobalCupProduct
