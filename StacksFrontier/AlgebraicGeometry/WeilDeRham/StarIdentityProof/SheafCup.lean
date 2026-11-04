module

public import StacksFrontier.AlgebraicGeometry.WeilDeRham.DiagonalCupStatements
public import StacksFrontier.AlgebraicGeometry.DeRham.KunnethWedge
public import StacksFrontier.AlgebraicGeometry.DeRham.KunnethWedgeSection
public import StacksFrontier.AlgebraicGeometry.DeRham.KunnethDifferential
public import StacksFrontier.AlgebraicGeometry.DeRham.DeRhamFormsToRelative
public import StacksFrontier.AlgebraicGeometry.DeRham.CupProduct.GradedCommutativity
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.PullbackHgroupRetraction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerShortExact
public import StacksFrontier.AlgebraicGeometry.Variety.Tangent.RelativeEmbeddingDimensionForms

/-!
# The cup product along a multiplication of sheaves, and section formulas

The cup product of Cohomology, Section 0FKU on a scheme along a multiplication of sheaves
(`Stacks.WeilDeRham.sheafCup`) and its naturality (`Stacks.WeilDeRham.sheafCup_naturality`), and
formulas for local sections of sheaves of modules and graded algebras used in the proof of the
identity `(★)` of [Stacks, Tag 0G8J].

## References

* [Stacks Project, Tag 0G8J](https://stacks.math.columbia.edu/tag/0G8J)
* [Stacks Project, Section 0FKU](https://stacks.math.columbia.edu/tag/0FKU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open RingedSpaceModuleAdjunction Stacks.Gysin Stacks.DeRham.GysinCohomologyBaseChange
open AlgebraicGeometry.Scheme.Hom Stacks.DeRham.CohomologicalGysin
open Stacks.DeRham.GysinCupHodge
open Stacks.SheafOfModules.Tensor (sheafTensor)
open Stacks.Cohomology.GlobalKunneth (baseSections baseRing)
open Stacks.Cohomology.DerivedGlobalCupProduct (cohomologyModule)
open AlgebraicGeometry.SheafOfModules (moduleDerived canonicalPairingModule tensorBifunctorNat
  baseRingedSpace multiplicationInt)
open scoped Stacks.StandardDerivedModel

universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose structureSheafRing
  AlgebraicGeometry.SheafedSpace.sheaf AlgebraicGeometry.SheafOfModules.baseRingedSpace
  Stacks.SheafOfModules.Tensor.ringSheaf

namespace Stacks.WeilDeRham

attribute [local instance] Stacks.Topology.RingedSpaceSheafifyOpens.opensHasSheafifyAddCommGrpCat
  Stacks.Topology.RingedSpaceSheafifyOpens.opensWEqualsLocallyBijectiveAddCommGrpCat
attribute [local instance] Stacks.DeRham.CohomologicalGysin.moduleSheavesHasDerivedCategory
attribute [local instance] AlgebraicGeometry.SheafOfModules.abelianModules
  AlgebraicGeometry.SheafOfModules.hasSheafifyOpens
  AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijectiveOpens

/-! ### The cup product along a multiplication of sheaves -/

section Cup

variable {Y : RingedSpace.{u, u}}

/-- The algebra of `singleTensorMult_whiskerLeft`, at variables. -/
private lemma bif_chase_left {C : Type*} [Category* C] (T : C ⥤ C ⥤ C) {a A b b' B B' H Hn : C}
    (sA : a ≅ A) (sG : b ≅ B) (sG' : b' ≅ B') (g : B ⟶ B') (w : (T.obj A).obj B' ⟶ H)
    (k : H ⟶ Hn) :
    (T.obj a).map sG.hom ≫ (T.map sA.hom).app B ≫ ((T.obj A).map g ≫ w) ≫ k =
      (T.obj a).map (sG.hom ≫ g ≫ sG'.inv) ≫ (T.obj a).map sG'.hom ≫ (T.map sA.hom).app B' ≫
        w ≫ k := by
  have n := (T.map sA.hom).naturality g
  simp only [Functor.map_comp, Category.assoc, ← Functor.map_comp_assoc (T.obj a) sG'.inv,
    Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]
  rw [reassoc_of% n]

/-- `singleTensorMult` precomposed with a morphism of the right factor. -/
theorem singleTensorMult_whiskerLeft
    {F G G' H : _root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Y.sheaf)}
    (g : G ⟶ G') (w : ((sheafTensor.{u, u, u, u, u} Y.sheaf).obj F).obj G' ⟶ H)
    (a b n : ℕ) (hn : a + b = n) :
    singleTensorMult (((sheafTensor.{u, u, u, u, u} Y.sheaf).obj F).map g ≫ w) a b n hn =
      ((tensorBifunctorNat (A := Y.sheaf)).obj (singleNat F a)).map
          ((HomologicalComplex.single _ (ComplexShape.up ℕ) b).map g) ≫
        singleTensorMult w a b n hn := by
  refine HomologicalComplex.to_single_hom_ext ?_
  refine HomologicalComplex.mapBifunctor.hom_ext fun (a' b' : ℕ) h => ?_
  by_cases hab : a' = a ∧ b' = b
  · obtain ⟨rfl, rfl⟩ := hab
    refine (ι_singleTensorMult_f _ a' b' n hn h).trans ?_
    have e := HomologicalComplex.ι_mapBifunctorMap (𝟙 (singleNat F a'))
      ((HomologicalComplex.single _ (ComplexShape.up ℕ) b').map g)
      (sheafTensor.{u, u, u, u, u} Y.sheaf) (ComplexShape.up ℕ) a' b' n h
    refine Eq.trans ?_ ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) e).trans
      ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans
        (congrArg (_ ≫ ·) (ι_singleTensorMult_f w a' b' n hn h)))))))).symm
    rw [HomologicalComplex.single_map_f_self, HomologicalComplex.id_f,
      CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp]
    exact bif_chase_left _ _ _ _ g w _
  · exact (isZero_singleNat_tensor_summand F G a b a' b' hab).eq_of_src _ _

variable {W : Scheme.{u}}

/-- The category of sheaves of modules on a scheme, in the spelling over the ring sheaf of the
tensor product of sheaves, in which the cup product of Section 0FKU is stated. -/
local notation "𝓜" W => _root_.SheafOfModules
  (Stacks.SheafOfModules.Tensor.ringSheaf (Scheme.sheaf W))

/-- **The cup product `Hᵠ(W, F) × Hʳ(W, G) ⟶ H^{q+r}(W, H)` along a multiplication
`m : F ⊗ G ⟶ H`** of Cohomology, Section 0FKU on `(W, 𝒪_W)`, both classes read through
`hgroupModuleShiftIso`. -/
def sheafCup {F G H : 𝓜 W} (m : ((sheafTensor W.sheaf).obj F).obj G ⟶ H) (q r : ℕ)
    (x : Hgroup (structureSheafRing W.toRingedSpace) ⊤ q F)
    (y : Hgroup (structureSheafRing W.toRingedSpace) ⊤ r G) :
    cohomologyModule (moduleDerived (A := W.sheaf) (singleNat (X := W.toRingedSpace) H 0))
      ((q : ℤ) + (r : ℤ)) :=
  (canonicalPairingModule (A := W.sheaf)
    (singleTensorMult (X := W.toRingedSpace) m 0 0 0 rfl) (q : ℤ) (r : ℤ)).hom
    ((hgroupModuleShiftIso (X := W.toRingedSpace) F 0 q q (by simp)).hom x ⊗ₜ
      (hgroupModuleShiftIso (X := W.toRingedSpace) G 0 r r (by simp)).hom y)

/-- The map induced on the cohomology of derived global sections by a morphism of sheaves placed
in degree `0`. -/
def singleCohomologyMap {H H' : 𝓜 W} (c : H ⟶ H') (k : ℤ) :
    cohomologyModule (moduleDerived (A := W.sheaf) (singleNat (X := W.toRingedSpace) H 0)) k ⟶
      cohomologyModule (moduleDerived (A := W.sheaf) (singleNat (X := W.toRingedSpace) H' 0)) k :=
  Stacks.Cohomology.DerivedGlobalCupProduct.cohomologyMap (S := baseRingedSpace W.sheaf)
    (HomologicalComplex.extendMap ((HomologicalComplex.single (𝓜 W)
      (ComplexShape.up ℕ) 0).map c) ComplexShape.embeddingUpNat) k

/-- **The cup product along a multiplication is natural in the three sheaves.** -/
theorem sheafCup_naturality {F F' G G' H H' : 𝓜 W} (a : F ⟶ F') (b : G ⟶ G')
    (c : H ⟶ H') (m : ((sheafTensor W.sheaf).obj F).obj G ⟶ H)
    (m' : ((sheafTensor W.sheaf).obj F').obj G' ⟶ H')
    (hm : m ≫ c = ((sheafTensor W.sheaf).obj F).map b ≫ ((sheafTensor W.sheaf).map a).app G' ≫ m')
    (q r : ℕ) (x : Hgroup (structureSheafRing W.toRingedSpace) ⊤ q F)
    (y : Hgroup (structureSheafRing W.toRingedSpace) ⊤ r G) :
    (singleCohomologyMap c ((q : ℤ) + (r : ℤ))).hom (sheafCup m q r x y) =
      sheafCup m' q r ((Hfunctor (structureSheafRing W.toRingedSpace) ⊤ q).map a x)
        ((Hfunctor (structureSheafRing W.toRingedSpace) ⊤ r).map b y) := by
  have hx := hgroupModuleShiftIso_naturality (X := W.toRingedSpace) a 0 q (q : ℤ) (by simp) x
  have hy := hgroupModuleShiftIso_naturality (X := W.toRingedSpace) b 0 r (r : ℤ) (by simp) y
  rw [moduleDerivedMap_singleFunctor_map (X := W.toRingedSpace) a] at hx
  rw [moduleDerivedMap_singleFunctor_map (X := W.toRingedSpace) b] at hy
  have hm' : singleTensorMult (X := W.toRingedSpace) m 0 0 0 rfl ≫
        (HomologicalComplex.single _ (ComplexShape.up ℕ) 0).map c =
      ((tensorBifunctorNat (A := W.sheaf)).obj (singleNat F 0)).map
          ((HomologicalComplex.single _ (ComplexShape.up ℕ) 0).map b) ≫
        ((tensorBifunctorNat (A := W.sheaf)).map
          ((HomologicalComplex.single _ (ComplexShape.up ℕ) 0).map a)).app (singleNat G' 0) ≫
        singleTensorMult (X := W.toRingedSpace) m' 0 0 0 rfl := by
    refine (singleTensorMult_comp (X := W.toRingedSpace) m c 0 0 0 rfl).symm.trans ?_
    rw [hm]
    refine (singleTensorMult_whiskerLeft (Y := W.toRingedSpace) b _ 0 0 0 rfl).trans ?_
    exact congrArg _ (singleTensorMult_whiskerRight (X := W.toRingedSpace) a m' 0 0 0 rfl)
  unfold sheafCup singleCohomologyMap
  rw [hx, hy]
  exact AlgebraicGeometry.SheafOfModules.canonicalPairingModule_naturality _ _ _ _ _ hm' (q : ℤ)
    (r : ℤ) _ _

/-- The map induced by a composite is the composite of the induced maps. -/
theorem singleCohomologyMap_comp {H H' H'' : 𝓜 W} (c : H ⟶ H') (d : H' ⟶ H'') (k : ℤ) :
    singleCohomologyMap (c ≫ d) k = singleCohomologyMap c k ≫ singleCohomologyMap d k := by
  unfold singleCohomologyMap Stacks.Cohomology.DerivedGlobalCupProduct.cohomologyMap
  rw [Functor.map_comp, HomologicalComplex.extendMap_comp, Functor.map_comp, Functor.map_comp,
    Functor.map_comp]

/-- The identity induces the identity. -/
theorem singleCohomologyMap_id (H : 𝓜 W) (k : ℤ) :
    singleCohomologyMap (𝟙 H) k = 𝟙 _ := by
  unfold singleCohomologyMap Stacks.Cohomology.DerivedGlobalCupProduct.cohomologyMap
  rw [CategoryTheory.Functor.map_id, HomologicalComplex.extendMap_id,
    CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]

/-- The map induced by a sum is the sum of the induced maps. -/
theorem singleCohomologyMap_add {H H' : 𝓜 W} (c d : H ⟶ H') (k : ℤ) :
    singleCohomologyMap (c + d) k = singleCohomologyMap c k + singleCohomologyMap d k := by
  unfold singleCohomologyMap
  rw [Functor.map_add, HomologicalComplex.extendMap_add,
    Stacks.Cohomology.DerivedGlobalCupProduct.cohomologyMap_add]

/-- The zero morphism induces zero. -/
theorem singleCohomologyMap_zero (H H' : 𝓜 W) (k : ℤ) :
    singleCohomologyMap (0 : H ⟶ H') k = 0 := by
  have h := singleCohomologyMap_add (0 : H ⟶ H') 0 k
  rw [add_zero] at h
  exact left_eq_add.mp h

/-- The cup product along a multiplication followed by a morphism of the target. -/
theorem sheafCup_comp {F G H H' : 𝓜 W} (m : ((sheafTensor W.sheaf).obj F).obj G ⟶ H)
    (c : H ⟶ H') (q r : ℕ) (x : Hgroup (structureSheafRing W.toRingedSpace) ⊤ q F)
    (y : Hgroup (structureSheafRing W.toRingedSpace) ⊤ r G) :
    sheafCup (m ≫ c) q r x y =
      (singleCohomologyMap c ((q : ℤ) + (r : ℤ))).hom (sheafCup m q r x y) := by
  have e₁ : (sheafTensor W.sheaf).map (𝟙 F) = 𝟙 _ := (sheafTensor W.sheaf).map_id F
  have e₂ : ((sheafTensor W.sheaf).obj F).map (𝟙 G) = 𝟙 _ :=
    ((sheafTensor W.sheaf).obj F).map_id G
  have e₃ : (Hfunctor (structureSheafRing W.toRingedSpace) ⊤ q).map (𝟙 F) = 𝟙 _ :=
    (Hfunctor (structureSheafRing W.toRingedSpace) ⊤ q).map_id F
  have e₄ : (Hfunctor (structureSheafRing W.toRingedSpace) ⊤ r).map (𝟙 G) = 𝟙 _ :=
    (Hfunctor (structureSheafRing W.toRingedSpace) ⊤ r).map_id G
  refine ((sheafCup_naturality (𝟙 F) (𝟙 G) c m (m ≫ c) ?_ q r x y).trans ?_).symm
  · rw [e₁, e₂, NatTrans.id_app, Category.id_comp, Category.id_comp]
  · rw [e₃, e₄]
    rfl

/-- The cup product of a class mapped along a morphism of the left factor. -/
theorem sheafCup_map_left {F F' G H : 𝓜 W} (a : F ⟶ F')
    (m : ((sheafTensor W.sheaf).obj F').obj G ⟶ H) (q r : ℕ)
    (x : Hgroup (structureSheafRing W.toRingedSpace) ⊤ q F)
    (y : Hgroup (structureSheafRing W.toRingedSpace) ⊤ r G) :
    sheafCup m q r ((Hfunctor (structureSheafRing W.toRingedSpace) ⊤ q).map a x) y =
      sheafCup (((sheafTensor W.sheaf).map a).app G ≫ m) q r x y := by
  have e₂ : ((sheafTensor W.sheaf).obj F).map (𝟙 G) = 𝟙 _ :=
    ((sheafTensor W.sheaf).obj F).map_id G
  have e₄ : (Hfunctor (structureSheafRing W.toRingedSpace) ⊤ r).map (𝟙 G) = 𝟙 _ :=
    (Hfunctor (structureSheafRing W.toRingedSpace) ⊤ r).map_id G
  have h := sheafCup_naturality a (𝟙 G) (𝟙 H) (((sheafTensor W.sheaf).map a).app G ≫ m) m
    (by rw [e₂, Category.id_comp, Category.comp_id]) q r x y
  rw [singleCohomologyMap_id, e₄] at h
  exact h.symm

/-- The cup product of a class mapped along a morphism of the right factor. -/
theorem sheafCup_map_right {F G G' H : 𝓜 W} (b : G ⟶ G')
    (m : ((sheafTensor W.sheaf).obj F).obj G' ⟶ H) (q r : ℕ)
    (x : Hgroup (structureSheafRing W.toRingedSpace) ⊤ q F)
    (y : Hgroup (structureSheafRing W.toRingedSpace) ⊤ r G) :
    sheafCup m q r x ((Hfunctor (structureSheafRing W.toRingedSpace) ⊤ r).map b y) =
      sheafCup (((sheafTensor W.sheaf).obj F).map b ≫ m) q r x y := by
  have e₁ : (sheafTensor W.sheaf).map (𝟙 F) = 𝟙 _ := (sheafTensor W.sheaf).map_id F
  have e₃ : (Hfunctor (structureSheafRing W.toRingedSpace) ⊤ q).map (𝟙 F) = 𝟙 _ :=
    (Hfunctor (structureSheafRing W.toRingedSpace) ⊤ q).map_id F
  have h := sheafCup_naturality (𝟙 F) b (𝟙 H) (((sheafTensor W.sheaf).obj F).map b ≫ m) m
    (by rw [e₁, NatTrans.id_app, Category.id_comp, Category.comp_id]) q r x y
  rw [singleCohomologyMap_id, e₃] at h
  exact h.symm

/-- The cup product along the zero multiplication vanishes. -/
theorem sheafCup_zero {F G H : 𝓜 W} (q r : ℕ)
    (x : Hgroup (structureSheafRing W.toRingedSpace) ⊤ q F)
    (y : Hgroup (structureSheafRing W.toRingedSpace) ⊤ r G) :
    sheafCup (0 : ((sheafTensor W.sheaf).obj F).obj G ⟶ H) q r x y = 0 := by
  have h := sheafCup_comp (0 : ((sheafTensor W.sheaf).obj F).obj G ⟶ H) (0 : H ⟶ H) q r x y
  rw [comp_zero, singleCohomologyMap_zero] at h
  exact h

/-- **Two classes agreeing on two jointly split components agree**: if `pr₁ ≫ v₁ + pr₂ ≫ v₂ = 𝟙`,
the maps induced by `pr₁` and `pr₂` are jointly injective. -/
theorem eq_of_singleCohomologyMap_eq {H T₁ T₂ : 𝓜 W} (pr₁ : H ⟶ T₁) (pr₂ : H ⟶ T₂)
    (v₁ : T₁ ⟶ H) (v₂ : T₂ ⟶ H) (hJ : pr₁ ≫ v₁ + pr₂ ≫ v₂ = 𝟙 H) (k : ℤ)
    {z z' : cohomologyModule
      (moduleDerived (A := W.sheaf) (singleNat (X := W.toRingedSpace) H 0)) k}
    (h₁ : (singleCohomologyMap pr₁ k).hom z = (singleCohomologyMap pr₁ k).hom z')
    (h₂ : (singleCohomologyMap pr₂ k).hom z = (singleCohomologyMap pr₂ k).hom z') : z = z' := by
  have e : ∀ w, w = (singleCohomologyMap v₁ k).hom ((singleCohomologyMap pr₁ k).hom w) +
      (singleCohomologyMap v₂ k).hom ((singleCohomologyMap pr₂ k).hom w) := fun w => by
    have := congrArg (fun φ => (singleCohomologyMap φ k).hom w) hJ
    simp only [singleCohomologyMap_add, singleCohomologyMap_comp, singleCohomologyMap_id] at this
    exact this.symm
  rw [e z, e z', h₁, h₂]

/-- The `pr`-component of a cup product with a class mapped along `α` is a cup product. -/
private theorem singleCohomologyMap_sheafCup_map_left {P Ωe Ωn Ω T Q : 𝓜 W} (α : P ⟶ Ωe)
    (μ : ((sheafTensor W.sheaf).obj Ωe).obj Ωn ⟶ Ω) (pr : Ω ⟶ T) (π₀ : Ωn ⟶ Q)
    (τ : ((sheafTensor W.sheaf).obj P).obj Q ⟶ T)
    (hS : ((sheafTensor W.sheaf).map α).app Ωn ≫ μ ≫ pr =
      ((sheafTensor W.sheaf).obj P).map π₀ ≫ τ)
    (q r : ℕ) (u : Hgroup (structureSheafRing W.toRingedSpace) ⊤ q P)
    (y : Hgroup (structureSheafRing W.toRingedSpace) ⊤ r Ωn) :
    (singleCohomologyMap pr _).hom
        (sheafCup μ q r ((Hfunctor (structureSheafRing W.toRingedSpace) ⊤ q).map α u) y) =
      (singleCohomologyMap τ _).hom (sheafCup (𝟙 _) q r u
        ((Hfunctor (structureSheafRing W.toRingedSpace) ⊤ r).map π₀ y)) := by
  rw [sheafCup_map_left, ← sheafCup_comp, sheafCup_map_right, ← sheafCup_comp,
    Category.assoc, hS, Category.comp_id]

/-- The `pr`-component of a cross product vanishes when the corresponding composite is zero. -/
private theorem singleCohomologyMap_sheafCup_map_eq_zero {P Q Ωe Ωn Ω T : 𝓜 W} (β : P ⟶ Ωe)
    (μ : ((sheafTensor W.sheaf).obj Ωe).obj Ωn ⟶ Ω) (pr : Ω ⟶ T) (αn : Q ⟶ Ωn)
    (hS : ((sheafTensor W.sheaf).obj P).map αn ≫ ((sheafTensor W.sheaf).map β).app Ωn ≫ μ ≫
      pr = 0)
    (q r : ℕ) (u : Hgroup (structureSheafRing W.toRingedSpace) ⊤ q P)
    (x : Hgroup (structureSheafRing W.toRingedSpace) ⊤ r Q) :
    (singleCohomologyMap pr _).hom
      (sheafCup μ q r ((Hfunctor (structureSheafRing W.toRingedSpace) ⊤ q).map β u)
        ((Hfunctor (structureSheafRing W.toRingedSpace) ⊤ r).map αn x)) = 0 := by
  rw [sheafCup_map_left, sheafCup_map_right, ← sheafCup_comp, Category.assoc, Category.assoc,
    hS, sheafCup_zero]

/-- **The identity `(★)` from its two components.** Let `μ : Ωᵉ ⊗ Ωⁿ ⟶ Ω` be a multiplication
and `pr₁ : Ω ⟶ T₁`, `pr₂ : Ω ⟶ T₂` jointly split. Suppose that after `α : P₁ ⟶ Ωᵉ` the
product with a class of `Ωⁿ` has `pr₁`-component the cup product with its image under
`π₀ : Ωⁿ ⟶ Q₂` (and symmetrically for `β`, `pr₂`, `π₀'`), and that the products of the
classes coming from `β` with `αₙ` and from `α` with `βₙ` have no `pr₁`-, resp. `pr₂`-,
component. Then `α(u₁) ∪ η = α(u₁) ∪ βₙ(x₂) + β(u₂) ∪ αₙ(x₁)` as soon as
`α(u₁) ∪ η = β(u₂) ∪ η` and the cup products with `u₁`, `u₂` do not see the difference between
`η` and `βₙ(x₂)`, resp. `αₙ(x₁)`, after `π₀`, resp. `π₀'`. -/
theorem sheafCup_eq_add_of_components {P₁ P₂ Ωe Ωn Ω T₁ T₂ Q₁ Q₂ : 𝓜 W}
    (α : P₁ ⟶ Ωe) (β : P₂ ⟶ Ωe) (μ : ((sheafTensor W.sheaf).obj Ωe).obj Ωn ⟶ Ω)
    (pr₁ : Ω ⟶ T₁) (pr₂ : Ω ⟶ T₂) (v₁ : T₁ ⟶ Ω) (v₂ : T₂ ⟶ Ω)
    (hJ : pr₁ ≫ v₁ + pr₂ ≫ v₂ = 𝟙 Ω)
    (π₀ : Ωn ⟶ Q₂) (π₀' : Ωn ⟶ Q₁) (αn : Q₁ ⟶ Ωn) (βn : Q₂ ⟶ Ωn)
    (τ₁ : ((sheafTensor W.sheaf).obj P₁).obj Q₂ ⟶ T₁)
    (τ₂ : ((sheafTensor W.sheaf).obj P₂).obj Q₁ ⟶ T₂)
    (hS₁ : ((sheafTensor W.sheaf).map α).app Ωn ≫ μ ≫ pr₁ =
      ((sheafTensor W.sheaf).obj P₁).map π₀ ≫ τ₁)
    (hS₂ : ((sheafTensor W.sheaf).map β).app Ωn ≫ μ ≫ pr₂ =
      ((sheafTensor W.sheaf).obj P₂).map π₀' ≫ τ₂)
    (hS₃ : ((sheafTensor W.sheaf).obj P₂).map αn ≫ ((sheafTensor W.sheaf).map β).app Ωn ≫ μ ≫
      pr₁ = 0)
    (hS₄ : ((sheafTensor W.sheaf).obj P₁).map βn ≫ ((sheafTensor W.sheaf).map α).app Ωn ≫ μ ≫
      pr₂ = 0)
    (q r : ℕ) (u₁ : Hgroup (structureSheafRing W.toRingedSpace) ⊤ q P₁)
    (u₂ : Hgroup (structureSheafRing W.toRingedSpace) ⊤ q P₂)
    (η : Hgroup (structureSheafRing W.toRingedSpace) ⊤ r Ωn)
    (x₁ : Hgroup (structureSheafRing W.toRingedSpace) ⊤ r Q₁)
    (x₂ : Hgroup (structureSheafRing W.toRingedSpace) ⊤ r Q₂)
    (h₀ : sheafCup μ q r ((Hfunctor (structureSheafRing W.toRingedSpace) ⊤ q).map α u₁) η =
      sheafCup μ q r ((Hfunctor (structureSheafRing W.toRingedSpace) ⊤ q).map β u₂) η)
    (h₁ : sheafCup (𝟙 _) q r u₁ ((Hfunctor (structureSheafRing W.toRingedSpace) ⊤ r).map π₀ η) =
      sheafCup (𝟙 _) q r u₁ ((Hfunctor (structureSheafRing W.toRingedSpace) ⊤ r).map π₀
        ((Hfunctor (structureSheafRing W.toRingedSpace) ⊤ r).map βn x₂)))
    (h₂ : sheafCup (𝟙 _) q r u₂ ((Hfunctor (structureSheafRing W.toRingedSpace) ⊤ r).map π₀' η) =
      sheafCup (𝟙 _) q r u₂ ((Hfunctor (structureSheafRing W.toRingedSpace) ⊤ r).map π₀'
        ((Hfunctor (structureSheafRing W.toRingedSpace) ⊤ r).map αn x₁))) :
    sheafCup μ q r ((Hfunctor (structureSheafRing W.toRingedSpace) ⊤ q).map α u₁) η =
      sheafCup μ q r ((Hfunctor (structureSheafRing W.toRingedSpace) ⊤ q).map α u₁)
          ((Hfunctor (structureSheafRing W.toRingedSpace) ⊤ r).map βn x₂) +
        sheafCup μ q r ((Hfunctor (structureSheafRing W.toRingedSpace) ⊤ q).map β u₂)
          ((Hfunctor (structureSheafRing W.toRingedSpace) ⊤ r).map αn x₁) := by
  have c₁ := singleCohomologyMap_sheafCup_map_left α μ pr₁ π₀ τ₁ hS₁ q r u₁
  have c₂ := singleCohomologyMap_sheafCup_map_left β μ pr₂ π₀' τ₂ hS₂ q r u₂
  have c₃ := singleCohomologyMap_sheafCup_map_eq_zero β μ pr₁ αn hS₃ q r u₂ x₁
  have c₄ := singleCohomologyMap_sheafCup_map_eq_zero α μ pr₂ βn hS₄ q r u₁ x₂
  refine eq_of_singleCohomologyMap_eq pr₁ pr₂ v₁ v₂ hJ _ ?_ ?_
  · rw [map_add, c₃, add_zero, c₁, c₁, h₁]
  · rw [map_add, c₄, zero_add, h₀, c₂, c₂, h₂]

end Cup

/-! ### Section formulas -/

/-- A composite of three morphisms of sheaves of modules on a local section. -/
theorem comp₃_val_app {C : Type*} [Category C] {J : GrothendieckTopology C} {R : Sheaf J RingCat}
    {M₁ M₂ M₃ M₄ : _root_.SheafOfModules R} (a : M₁ ⟶ M₂) (b : M₂ ⟶ M₃) (c : M₃ ⟶ M₄)
    (U : Cᵒᵖ) (x : M₁.val.obj U) :
    (a ≫ b ≫ c).val.app U x = c.val.app U (b.val.app U (a.val.app U x)) :=
  rfl

/-- A composite of two morphisms of sheaves of modules on a local section. -/
theorem comp₂_val_app {C : Type*} [Category C] {J : GrothendieckTopology C} {R : Sheaf J RingCat}
    {M₁ M₂ M₃ : _root_.SheafOfModules R} (a : M₁ ⟶ M₂) (b : M₂ ⟶ M₃)
    (U : Cᵒᵖ) (x : M₁.val.obj U) :
    (a ≫ b).val.app U x = b.val.app U (a.val.app U x) :=
  rfl

section GradedHEq

variable {C : Type*} [Category C] {J : GrothendieckTopology C} {R : Sheaf J RingCat}
  (A : _root_.SheafOfModules.GradedAlgebra R) {U : Cᵒᵖ}

/-- The multiplication of a sheaf of graded algebras respects heterogeneous equality of its
arguments. -/
theorem mul_heq_mul {i i' j j' : ℤ} (hi : i = i') (hj : j = j')
    {x : (A.piece i).val.obj U} {x' : (A.piece i').val.obj U}
    {y : (A.piece j).val.obj U} {y' : (A.piece j').val.obj U} (hx : HEq x x') (hy : HEq y y') :
    HEq ((A.mul i j).app U x y) ((A.mul i' j').app U x' y') := by
  subst hi hj
  cases eq_of_heq hx
  cases eq_of_heq hy
  rfl

/-- Scalar multiplication respects heterogeneous equality. -/
theorem smul_heq_smul {i i' : ℤ} (h : i = i') (r : R.obj.obj U) {x : (A.piece i).val.obj U}
    {x' : (A.piece i').val.obj U} (hx : HEq x x') : HEq (r • x) (r • x') := by
  subst h
  cases eq_of_heq hx
  rfl

/-- Integer multiplication respects heterogeneous equality. -/
theorem zsmul_heq_zsmul {i i' : ℤ} (h : i = i') (c : ℤ) {x : (A.piece i).val.obj U}
    {x' : (A.piece i').val.obj U} (hx : HEq x x') : HEq (c • x) (c • x') := by
  subst h
  cases eq_of_heq hx
  rfl

/-- The zero sections of two equal pieces are heterogeneously equal. -/
theorem zero_heq_zero {i i' : ℤ} (h : i = i') :
    HEq (0 : (A.piece i).val.obj U) (0 : (A.piece i').val.obj U) := by
  subst h
  rfl

/-- A unital homomorphism respects heterogeneous equality. -/
theorem unitalHom_app_heq {B : _root_.SheafOfModules.GradedAlgebra R}
    (φ : _root_.SheafOfModules.GradedAlgebra.UnitalHom A B) {i i' : ℤ} (h : i = i')
    {x : (A.piece i).val.obj U} {x' : (A.piece i').val.obj U} (hx : HEq x x') :
    HEq ((φ.app i).val.app U x) ((φ.app i').val.app U x') := by
  subst h
  cases eq_of_heq hx
  rfl

end GradedHEq

/-- Transport along an equality of natural indices is heterogeneously the identity on local
sections. -/
theorem eqToHom_val_app_heq_nat {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat} (Y : ℕ → _root_.SheafOfModules R) {a b : ℕ} (h : a = b) (U : Cᵒᵖ)
    (x : (Y a).val.obj U) : HEq ((eqToHom (congrArg Y h)).val.app U x) x := by
  subst h
  rfl

section TensorSections

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] (Osharp : Sheaf J CommRingCat.{u})
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]

/-- The tensor product with a fixed left factor, on a local pure tensor. -/
theorem sheafTensor_obj_map_val_app_unit (F : _root_.SheafOfModules.{u} (Sheaf.toRingCat J Osharp))
    {G G' : _root_.SheafOfModules.{u} (Sheaf.toRingCat J Osharp)} (g : G ⟶ G') (V : Cᵒᵖ)
    (x : F.val.obj V) (y : G.val.obj V) :
    (((sheafTensor Osharp).obj F).map g).val.app V
        ((PresheafOfModules.tensorSheafUnit F G).app V (x ⊗ₜ y)) =
      (PresheafOfModules.tensorSheafUnit F G').app V (x ⊗ₜ g.val.app V y) := by
  have h := Stacks.TensorSheafWorld.tensorSheafBifunctor_map_val_app_tensorSheafUnit Osharp F G
    (𝟙 F) g V x y
  rw [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp] at h
  exact h

/-- The tensor product with a fixed right factor, on a local pure tensor. -/
theorem sheafTensor_map_app_val_app_unit
    {F F' : _root_.SheafOfModules.{u} (Sheaf.toRingCat J Osharp)}
    (a : F ⟶ F') (G : _root_.SheafOfModules.{u} (Sheaf.toRingCat J Osharp)) (V : Cᵒᵖ)
    (x : F.val.obj V) (y : G.val.obj V) :
    (((sheafTensor Osharp).map a).app G).val.app V
        ((PresheafOfModules.tensorSheafUnit F G).app V (x ⊗ₜ y)) =
      (PresheafOfModules.tensorSheafUnit F' G).app V (a.val.app V x ⊗ₜ y) := by
  have h := Stacks.TensorSheafWorld.tensorSheafBifunctor_map_val_app_tensorSheafUnit Osharp F G
    a (𝟙 G) V x y
  rw [CategoryTheory.Functor.map_id, Category.comp_id] at h
  exact h

/-- **Morphisms out of `F ⊗ G` are determined on the summands of a finite decomposition of `G`**:
if `∑ₖ pₖ ≫ iₖ = 𝟙 G`, two morphisms agreeing after each `F ◁ iₖ` are equal. -/
theorem tensor_hom_ext_of_sum_eq_id {ι : Type*} [Fintype ι]
    {F G Q : _root_.SheafOfModules.{u} (Sheaf.toRingCat J Osharp)}
    {B : ι → _root_.SheafOfModules.{u} (Sheaf.toRingCat J Osharp)} (i : ∀ k, B k ⟶ G)
    (p : ∀ k, G ⟶ B k) (hsum : ∑ k, p k ≫ i k = 𝟙 G)
    {φ ψ : ((sheafTensor Osharp).obj F).obj G ⟶ Q}
    (h : ∀ k, ((sheafTensor Osharp).obj F).map (i k) ≫ φ =
      ((sheafTensor Osharp).obj F).map (i k) ≫ ψ) : φ = ψ := by
  refine PresheafOfModules.tensorSheaf_hom_ext fun U x ω => ?_
  have hω : ∑ k, (i k).val.app U ((p k).val.app U ω) = ω := by
    let ev : (G ⟶ G) →+ G.val.obj U :=
      { toFun := fun χ => χ.val.app U ω
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    have h' := congrArg ev hsum
    rw [map_sum] at h'
    exact h'
  let g : ∀ χ : ((sheafTensor Osharp).obj F).obj G ⟶ Q, G.val.obj U →+ Q.val.obj U :=
    fun χ => ((χ.val.app U).hom.toAddMonoidHom.comp
      ((PresheafOfModules.tensorSheafUnit F G).app U).hom.toAddMonoidHom).comp
        (TensorProduct.mk ((Osharp.obj ⋙ forget₂ CommRingCat RingCat).obj U) (F.val.obj U)
          (G.val.obj U) x).toAddMonoidHom
  show g φ ω = g ψ ω
  rw [← hω, map_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  show φ.val.app U ((PresheafOfModules.tensorSheafUnit F G).app U
      (x ⊗ₜ (i k).val.app U ((p k).val.app U ω))) =
    ψ.val.app U ((PresheafOfModules.tensorSheafUnit F G).app U
      (x ⊗ₜ (i k).val.app U ((p k).val.app U ω)))
  rw [← sheafTensor_obj_map_val_app_unit Osharp F (i k) U x ((p k).val.app U ω)]
  exact congrArg (fun χ => χ.val.app U ((PresheafOfModules.tensorSheafUnit F (B k)).app U
    (x ⊗ₜ (p k).val.app U ω))) (h k)

end TensorSections

section PullbackComparison

open _root_.SheafOfModules.GradedAlgebra

variable {Y₁ Y₂ : RingedSpace.{u, u}} (g : Y₁ ⟶ Y₂)

/-- The pullback of a morphism on the pullback-unit image of a local section is the
pullback-unit image of its value. -/
theorem modulePullback_map_unit_val_app {M N : _root_.SheafOfModules.{u} (structureSheafRing Y₂)}
    (φ : M ⟶ N) (U : (Opens Y₂.carrier)ᵒᵖ) (x : M.val.obj U) :
    ((modulePullback g).map φ).val.app ((opensMap g).op.obj U)
        (((modulePullbackPushforwardAdjunction g).unit.app M).val.app U x) =
      ((modulePullbackPushforwardAdjunction g).unit.app N).val.app U (φ.val.app U x) := by
  have e : (modulePullbackPushforwardAdjunction g).homEquiv M _ ((modulePullback g).map φ) =
      φ ≫ (modulePullbackPushforwardAdjunction g).unit.app N :=
    ((modulePullbackPushforwardAdjunction g).homEquiv_unit _ _ _).trans
      ((modulePullbackPushforwardAdjunction g).unit_naturality φ)
  exact (homEquiv_val_app g _ U x).symm.trans (congrArg (fun ψ => ψ.val.app U x) e)

variable {F F' : _root_.SheafOfModules.{u} (structureSheafRing Y₂)}
  {A A' : _root_.SheafOfModules.GradedAlgebra.{u, u} (structureSheafRing Y₂)} {ι : F ⟶ A.piece 1}
  {ι' : F' ⟶ A'.piece 1} {B : _root_.SheafOfModules.GradedAlgebra.{u, u} (structureSheafRing Y₁)}
  {κ : (modulePullback g).obj F ⟶ B.piece 1} {κ' : (modulePullback g).obj F' ⟶ B.piece 1}

/-- **The comparison of Tag 01CI after the map of exterior algebras induced by `ρ : F ⟶ F'`** is
the comparison for the composite generator: precomposing the comparison for `κ'` with the
pullback of the map of exterior algebras induced by `ρ` gives the comparison for
`g^*ρ ≫ κ'`. -/
theorem modulePullback_map_comp_pullbackComparison (hA : IsExteriorAlgebra A ι)
    (hA' : IsExteriorAlgebra A' ι') (hκ : SquareZero κ) (hκ' : SquareZero κ') (ρ : F ⟶ F')
    (hρ : (modulePullback g).map ρ ≫ κ' = κ) (n : ℤ) :
    (modulePullback g).map ((hA.map hA' ρ).app n) ≫ pullbackComparison g hA' hκ' n =
      pullbackComparison g hA hκ n := by
  have key : ∀ (m : ℤ) (U : (Opens Y₂.carrier)ᵒᵖ) (z : (A.piece m).val.obj U)
      (z' : (A'.piece m).val.obj U), ((hA.map hA' ρ).app m).val.app U z = z' →
      ((modulePullback g).map ((hA.map hA' ρ).app m) ≫ pullbackComparison g hA' hκ' m).val.app
          ((opensMap g).op.obj U)
          (((modulePullbackPushforwardAdjunction g).unit.app (A.piece m)).val.app U z) =
        (pullbackComparison g hA' hκ' m).val.app ((opensMap g).op.obj U)
          (((modulePullbackPushforwardAdjunction g).unit.app (A'.piece m)).val.app U z') := by
    rintro m U z - rfl
    exact congrArg ((pullbackComparison g hA' hκ' m).val.app ((opensMap g).op.obj U))
      (modulePullback_map_unit_val_app g _ U z)
  refine pullbackComparison_unique g hA hκ
    (fun n => (modulePullback g).map ((hA.map hA' ρ).app n) ≫ pullbackComparison g hA' hκ' n)
    (fun i j U a b => ?_) (fun U => ?_) (fun U s => ?_) n
  · refine (key _ U _ _ ((hA.map hA' ρ).map_mul i j U a b)).trans ?_
    refine (pullbackComparison_mul g hA' hκ' i j U _ _).trans ?_
    exact congrArg₂ (fun y z => (B.mul i j).app ((opensMap g).op.obj U) y z)
      (congrArg ((pullbackComparison g hA' hκ' i).val.app ((opensMap g).op.obj U))
        (modulePullback_map_unit_val_app g _ U a).symm)
      (congrArg ((pullbackComparison g hA' hκ' j).val.app ((opensMap g).op.obj U))
        (modulePullback_map_unit_val_app g _ U b).symm)
  · exact (key 0 U _ _ ((hA.map hA' ρ).map_one U)).trans (pullbackComparison_one g hA' hκ' U)
  · have h₁ : ((hA.map hA' ρ).app 1).val.app U (ι.val.app U s) = ι'.val.app U (ρ.val.app U s) :=
      congrArg (fun φ : F ⟶ A'.piece 1 => φ.val.app U s) (hA.map_app_one hA' ρ)
    refine (key 1 U _ _ h₁).trans ?_
    refine (pullbackComparison_generator g hA' hκ' U _).trans ?_
    refine (congrArg (κ'.val.app ((opensMap g).op.obj U))
      (modulePullback_map_unit_val_app g ρ U s).symm).trans ?_
    exact congrArg (fun φ : (modulePullback g).obj F ⟶ B.piece 1 => φ.val.app
      ((opensMap g).op.obj U) (((modulePullbackPushforwardAdjunction g).unit.app F).val.app U s))
      hρ

end PullbackComparison

end Stacks.WeilDeRham

end
