module

public import StacksFrontier.Topology.Sheaves.Cohomology.CechToCohomology.AcyclicCovering
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.ModuleCupProduct

/-!
# The sheaf-tensor coefficient pairing, and the Čech cup product it carries

Let `X` be a space carrying a sheaf `𝒪_X` of commutative rings, let `V` be an open subset and
put `A = 𝒪_X(V)`.  This file constructs the pairing of the coefficient sections presheaves that
the tensor product of sheaves of `𝒪_X`-modules gives, which is the one Stacks Tag 0FKV displays.
For each open `Z ≤ V` it is the base-change map

`K(Z) ⊗_A L(Z) ⟶ K(Z) ⊗_{𝒪_X(Z)} L(Z)`

followed by the unit of sheafification, so the source tensors over the *ring* `A` of sections on
`V` while the target's coefficients tensor over the *structure sheaf*.  The Čech cup product
`Stacks.Cech.ModuleCupProduct.cechCupProductA` at this pairing is the left-hand column of the
diagram of Tag 0FKV.

## Main definitions

* `Stacks.Cech.SheafTensorPairing.baseChange` is the base-change map
  `M ⊗_A N ⟶ M ⊗_B N` for a ring homomorphism `A ⟶ B` and `B`-modules `M`, `N`.
* `Stacks.Cech.SheafTensorPairing.basePairing` is the resulting pairing of the sections of two
  presheaves of `𝒪_X`-modules into the sections of their pointwise tensor product over the
  structure sheaf.
* `Stacks.Cech.SheafTensorPairing.sheafTensorPairing` is the pairing at sheaves of
  `𝒪_X`-modules: the base-change pairing followed by sheafification.
* `Stacks.Cech.SheafTensorPairing.sheafTensorComplexPairing` is the induced pairing of
  complexes, with target the totalization `Tot(K ⊗_{𝒪_X} L)` of the tensor bicomplex.
* `Stacks.Cech.SheafTensorPairing.cechCupProductSheafTensor` is the Čech cup product at that
  pairing: the left-hand column of Tag 0FKV.

## Main results

* `baseChange_tmul` and `basePairing_app` compute the base-change pairing.
* `basePairing_naturality_left`, `basePairing_naturality_right`,
  `sheafTensorPairing_naturality_left` and `sheafTensorPairing_naturality_right` are the
  naturality of the pairing in the two coefficient arguments.
* `ιMapBifunctor_d` is the differential of `Tot(K ⊗_{𝒪_X} L)` on a homogeneous summand.

## References

* [Stacks Project, Tag 07MB](https://stacks.math.columbia.edu/tag/07MB)
* [Stacks Project, Tag 0FKV](https://stacks.math.columbia.edu/tag/0FKV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape MonoidalCategory Opposite
  TopologicalSpace
open Stacks.Cohomology.CechSheaf
open Stacks.Cech.CupProduct (tensorModules)
open Stacks.SheafOfModules.Tensor (ringSheaf sheafTensor)
open Stacks.Cech.LinearCupProduct
open Stacks.Cech.ModuleCupProduct

open scoped TensorProduct

universe u

namespace Stacks.Cech.SheafTensorPairing

/-! ### Base change of a tensor product of modules -/

section BaseChange

variable {A B : Type u} [CommRing A] [CommRing B] (ψ : A →+* B) (M N : ModuleCat.{u} B)

/-- **The bilinear map underlying base change.**  For a ring homomorphism `ψ : A ⟶ B` and two
`B`-modules `M` and `N`, the map `(x, y) ↦ x ⊗ y` is `A`-bilinear for the `A`-module structures
obtained by restricting scalars along `ψ`. -/
noncomputable def baseChangeBilinear :
    ((ModuleCat.restrictScalars ψ).obj M) →ₗ[A] ((ModuleCat.restrictScalars ψ).obj N) →ₗ[A]
      ((ModuleCat.restrictScalars ψ).obj (M ⊗ N)) where
  toFun x :=
    { toFun := fun y => TensorProduct.mk B (M : Type u) (N : Type u) x y
      map_add' := fun y y' => (TensorProduct.mk B (M : Type u) (N : Type u) x).map_add y y'
      map_smul' := fun a y =>
        (TensorProduct.mk B (M : Type u) (N : Type u) x).map_smul (ψ a) y }
  map_add' x x' := LinearMap.ext fun y => TensorProduct.add_tmul x x' y
  map_smul' _ _ := LinearMap.ext fun _ => rfl

/-- **The base-change map `M ⊗_A N ⟶ M ⊗_B N`** along a ring homomorphism `ψ : A ⟶ B`, for
`B`-modules `M` and `N` read as `A`-modules by restriction of scalars.  It is the canonical
surjection identifying the two tensor products relative to the `B`-balanced relation. -/
noncomputable def baseChange :
    ModuleCat.of A (((ModuleCat.restrictScalars ψ).obj M) ⊗[A]
        ((ModuleCat.restrictScalars ψ).obj N)) ⟶
      (ModuleCat.restrictScalars ψ).obj (M ⊗ N) :=
  ConcreteCategory.ofHom (C := ModuleCat A) (TensorProduct.lift (baseChangeBilinear ψ M N))

/-- Base change takes a pure tensor over `A` to the same pure tensor over `B`. -/
@[simp]
theorem baseChange_tmul (x : M) (y : N) :
    (baseChange ψ M N).hom (x ⊗ₜ[A] y) = (x ⊗ₜ[B] y : (M ⊗ N : ModuleCat B)) :=
  rfl

end BaseChange

variable {X : Type u} [TopologicalSpace X]
  (O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}) (V : Opens X)

attribute [local instance] ModuleCat.hasLimitsOfSize ModuleCat.hasColimitsOfSize

/-! ### The structure sheaf and its pointwise tensor product -/

/-- The `RingCat`-valued presentation of the structure sheaf used by `SheafOfModules` is, on the
nose, the composite of `𝒪_X` with `forget₂ CommRingCat RingCat`. -/
theorem ringSheaf_obj : (ringSheaf O).obj = O.obj ⋙ forget₂ CommRingCat RingCat := rfl

/-- **The pointwise tensor product over the structure sheaf** of the underlying presheaves of
modules of two sheaves of `𝒪_X`-modules: the presheaf `Z ↦ F(Z) ⊗_{𝒪_X(Z)} G(Z)`, whose
sheafification is `F ⊗_{𝒪_X} G`. -/
noncomputable abbrev presheafTensorObj (F G : Modules O) :
    PresheafOfModules.{u} (ringSheaf O).obj :=
  ((PresheafOfModules.tensorBifunctor O.obj).obj F.val).obj G.val

/-- A morphism of sheaves of `𝒪_X`-modules, tensored on the right with a fixed sheaf, at the
level of the pointwise tensor product of the underlying presheaves of modules.  This is the
presheaf-level map that `(sheafTensor O).map f` sheafifies. -/
noncomputable abbrev presheafTensorMapLeft {F F' : Modules O} (f : F ⟶ F') (G : Modules O) :
    presheafTensorObj O F G ⟶ presheafTensorObj O F' G :=
  ((PresheafOfModules.tensorBifunctor O.obj).map f.val).app G.val

/-- A morphism of sheaves of `𝒪_X`-modules, tensored on the left with a fixed sheaf, at the
level of the pointwise tensor product of the underlying presheaves of modules.  This is the
presheaf-level map that `((sheafTensor O).obj F).map g` sheafifies. -/
noncomputable abbrev presheafTensorMapRight (F : Modules O) {G G' : Modules O} (g : G ⟶ G') :
    presheafTensorObj O F G ⟶ presheafTensorObj O F G' :=
  ((PresheafOfModules.tensorBifunctor O.obj).obj F.val).map g.val

/-- The open subset underlying an object of the slice site over `V`. -/
abbrev sliceOpen (Z : (Over V)ᵒᵖ) : (Opens X)ᵒᵖ := op Z.unop.left

/-- **The restriction homomorphism `𝒪_X(V) ⟶ 𝒪_X(Z)`** for an open `Z ≤ V`, along which the
sections of a sheaf of `𝒪_X`-modules on `Z` become a module over the coefficient ring
`A = 𝒪_X(V)`. -/
noncomputable abbrev coeffRestriction (Z : (Over V)ᵒᵖ) :
    CoeffRing O V →+* ((O.obj ⋙ forget₂ CommRingCat RingCat).obj (sliceOpen V Z)) :=
  (((ringSheaf O).over V).obj.map (IsInitial.to Over.mkIdTerminal.op Z)).hom

/-- **Restriction to the opens over `V`, for presheaves of `𝒪_X`-modules**, read as presheaves
of `A`-modules: `Stacks.Cech.ModuleCupProduct.sectionsFunctor` with the sheaf condition dropped. -/
noncomputable abbrev sectionsPresheafModules :
    PresheafOfModules.{u} (ringSheaf O).obj ⥤ PresheafModules.{u} (Over V) (CoeffRing O V) :=
  PresheafOfModules.pushforward (F := Over.forget V) (𝟙 ((ringSheaf O).over V).obj) ⋙
    PresheafOfModules.forgetToPresheafModuleCat (op (Over.mk (𝟙 V))) Over.mkIdTerminal.op

/-- Taking sections over the opens below `V` of a *sheaf* of `𝒪_X`-modules is taking them of its
underlying presheaf of modules. -/
theorem sectionsFunctor_eq :
    sectionsFunctor O V = SheafOfModules.forget (ringSheaf O) ⋙ sectionsPresheafModules O V :=
  rfl

/-! ### The base-change pairing at presheaf coefficients -/

variable (P Q : PresheafOfModules.{u} (ringSheaf O).obj)

/-- **The base-change pairing.**  For presheaves `P` and `Q` of `𝒪_X`-modules, the pairing of
their sections over the ring `A = 𝒪_X(V)` into the sections of their pointwise tensor product
over the structure sheaf: on an open `Z ≤ V` it is `P(Z) ⊗_A Q(Z) ⟶ P(Z) ⊗_{𝒪_X(Z)} Q(Z)`. -/
noncomputable def basePairing :
    Pairing.{u} (CoeffRing O V) ((sectionsPresheafModules O V).obj P)
      ((sectionsPresheafModules O V).obj Q)
      ((sectionsPresheafModules O V).obj
        (((PresheafOfModules.tensorBifunctor O.obj).obj P).obj Q)) where
  app Z := baseChange (coeffRestriction O V Z) (P.obj (sliceOpen V Z)) (Q.obj (sliceOpen V Z))
  naturality _ _ _ := ModuleCat.hom_ext <| TensorProduct.ext' fun _ _ => rfl

/-- The base-change pairing is, on each open below `V`, the base-change map of modules. -/
theorem basePairing_app (Z : (Over V)ᵒᵖ) :
    (basePairing O V P Q).app Z =
      baseChange (coeffRestriction O V Z) (P.obj (sliceOpen V Z)) (Q.obj (sliceOpen V Z)) :=
  rfl

variable {P Q}

/-- The base-change pairing is natural in the first coefficient presheaf. -/
theorem basePairing_naturality_left {P P' : PresheafOfModules.{u} (ringSheaf O).obj} (f : P ⟶ P')
    (Q : PresheafOfModules.{u} (ringSheaf O).obj) :
    ((tensorPresheafModules.{u} (CoeffRing O V)).map ((sectionsPresheafModules O V).map f)).app
          ((sectionsPresheafModules O V).obj Q) ≫ basePairing O V P' Q =
      basePairing O V P Q ≫
        (sectionsPresheafModules O V).map
          (((PresheafOfModules.tensorBifunctor O.obj).map f).app Q) :=
  NatTrans.ext <| funext fun _ => ModuleCat.hom_ext <| TensorProduct.ext' fun _ _ => rfl

/-- The base-change pairing is natural in the second coefficient presheaf. -/
theorem basePairing_naturality_right (P : PresheafOfModules.{u} (ringSheaf O).obj)
    {Q Q' : PresheafOfModules.{u} (ringSheaf O).obj} (g : Q ⟶ Q') :
    (((tensorPresheafModules.{u} (CoeffRing O V)).obj
            ((sectionsPresheafModules O V).obj P)).map
          ((sectionsPresheafModules O V).map g)) ≫ basePairing O V P Q' =
      basePairing O V P Q ≫
        (sectionsPresheafModules O V).map
          (((PresheafOfModules.tensorBifunctor O.obj).obj P).map g) :=
  NatTrans.ext <| funext fun _ => ModuleCat.hom_ext <| TensorProduct.ext' fun _ _ => rfl

/-! ### The pairing at sheaf coefficients -/

/-- **Sheafification of presheaves of `𝒪_X`-modules, followed by taking sections again**: the
endofunctor of which the sheafification unit is the unit, i.e. the composite appearing in
`PresheafOfModules.sheafificationAdjunction`. -/
noncomputable abbrev sheafifyComp :
    PresheafOfModules.{u} (ringSheaf O).obj ⥤ PresheafOfModules.{u} (ringSheaf O).obj :=
  PresheafOfModules.sheafification (𝟙 (ringSheaf O).obj) ⋙
    SheafOfModules.forget (ringSheaf O) ⋙
      PresheafOfModules.restrictScalars (𝟙 (ringSheaf O).obj)

/-- **The unit of sheafification** on the pointwise tensor product of the underlying presheaves
of modules of two sheaves of `𝒪_X`-modules. -/
noncomputable abbrev sheafifyUnit (F G : Modules O) :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf O).obj)).unit.app
    (presheafTensorObj O F G)

/-- The sheaf tensor product is the sheafification of the pointwise tensor product of the
underlying presheaves of modules, on the nose. -/
theorem sheafTensor_obj_obj (F G : Modules O) :
    ((sheafTensor O).obj F).obj G = (PresheafOfModules.sheafification
        (R₀ := (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)
        (R := Stacks.SheafOfModules.Tensor.ringSheaf O)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).obj (presheafTensorObj O F G) :=
  rfl

/-- **The sheaf-tensor coefficient pairing.**  For sheaves `F` and `G` of `𝒪_X`-modules, the
pairing of their sections over `A = 𝒪_X(V)` into the sections of `F ⊗_{𝒪_X} G`: base change from
`A` to `𝒪_X(Z)` on each open `Z ≤ V`, followed by the unit of sheafification.

This is the coefficient pairing of Stacks Tag 0FKV: the source tensors over the ring `A`, the
target's coefficients over the structure sheaf. -/
noncomputable def sheafTensorPairing (F G : Modules O) :
    Pairing.{u} (CoeffRing O V) ((sectionsFunctor O V).obj F) ((sectionsFunctor O V).obj G)
      ((sectionsFunctor O V).obj (((sheafTensor O).obj F).obj G)) :=
  basePairing O V F.val G.val ≫ (sectionsPresheafModules O V).map (sheafifyUnit O F G)

/-- The sheaf-tensor pairing is the base-change pairing followed by sheafification. -/
theorem sheafTensorPairing_eq (F G : Modules O) :
    sheafTensorPairing O V F G =
      basePairing O V F.val G.val ≫
        (sectionsPresheafModules O V).map (sheafifyUnit O F G) :=
  rfl

/-- Sections of the sheafification unit are natural in a morphism of pointwise tensor products. -/
private theorem map_sheafifyUnit_comp_naturality {F F' G G' : Modules O}
    (φ : presheafTensorObj O F G ⟶ presheafTensorObj O F' G') :
    (sectionsPresheafModules O V).map φ ≫
        (sectionsPresheafModules O V).map (sheafifyUnit O F' G') =
      (sectionsPresheafModules O V).map (sheafifyUnit O F G) ≫
        (sectionsPresheafModules O V).map ((sheafifyComp O).map φ) := by
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg _
    ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf O).obj)).unit.naturality φ)

/-- The sheaf-tensor pairing is natural in the first coefficient sheaf. -/
theorem sheafTensorPairing_naturality_left {F F' : Modules O} (f : F ⟶ F') (G : Modules O) :
    ((tensorPresheafModules.{u} (CoeffRing O V)).map ((sectionsFunctor O V).map f)).app
          ((sectionsFunctor O V).obj G) ≫ sheafTensorPairing O V F' G =
      sheafTensorPairing O V F G ≫
        (sectionsFunctor O V).map (((sheafTensor O).map f).app G) := by
  show ((tensorPresheafModules.{u} (CoeffRing O V)).map
        ((sectionsPresheafModules O V).map f.val)).app
          ((sectionsPresheafModules O V).obj G.val) ≫
        (basePairing O V F'.val G.val ≫
          (sectionsPresheafModules O V).map (sheafifyUnit O F' G)) =
      (basePairing O V F.val G.val ≫
          (sectionsPresheafModules O V).map (sheafifyUnit O F G)) ≫
        (sectionsPresheafModules O V).map ((sheafifyComp O).map (presheafTensorMapLeft O f G))
  rw [← Category.assoc, basePairing_naturality_left O V f.val G.val,
    Category.assoc, Category.assoc]
  exact congrArg (basePairing O V F.val G.val ≫ ·)
    (map_sheafifyUnit_comp_naturality O V (presheafTensorMapLeft O f G))

/-- The sheaf-tensor pairing is natural in the second coefficient sheaf. -/
theorem sheafTensorPairing_naturality_right (F : Modules O) {G G' : Modules O} (g : G ⟶ G') :
    (((tensorPresheafModules.{u} (CoeffRing O V)).obj ((sectionsFunctor O V).obj F)).map
          ((sectionsFunctor O V).map g)) ≫ sheafTensorPairing O V F G' =
      sheafTensorPairing O V F G ≫
        (sectionsFunctor O V).map (((sheafTensor O).obj F).map g) := by
  show (((tensorPresheafModules.{u} (CoeffRing O V)).obj
        ((sectionsPresheafModules O V).obj F.val)).map
          ((sectionsPresheafModules O V).map g.val)) ≫
        (basePairing O V F.val G'.val ≫
          (sectionsPresheafModules O V).map (sheafifyUnit O F G')) =
      (basePairing O V F.val G.val ≫
          (sectionsPresheafModules O V).map (sheafifyUnit O F G)) ≫
        (sectionsPresheafModules O V).map ((sheafifyComp O).map (presheafTensorMapRight O F g))
  rw [← Category.assoc, basePairing_naturality_right O V F.val g.val,
    Category.assoc, Category.assoc]
  exact congrArg (basePairing O V F.val G.val ≫ ·)
    (map_sheafifyUnit_comp_naturality O V (presheafTensorMapRight O F g))

/-! ### The pairing of complexes -/

variable (K L : CochainComplex (Modules O) ℤ)
  [(sheafTensor O).Additive] [∀ F : Modules O, ((sheafTensor O).obj F).Additive]
  [HomologicalComplex.HasMapBifunctor K L (sheafTensor O) (up ℤ)]

/-- **The differential of `Tot(K ⊗_{𝒪_X} L)` on a homogeneous summand**: the coefficient
differential of each factor, with the Koszul sign. -/
theorem ιMapBifunctor_d (a b n : ℤ) (h : a + b = n) :
    HomologicalComplex.ιMapBifunctor K L (sheafTensor O) (up ℤ) a b n h ≫
        (HomologicalComplex.mapBifunctor K L (sheafTensor O) (up ℤ)).d n (n + 1) =
      ((sheafTensor O).map (K.d a (a + 1))).app (L.X b) ≫
          HomologicalComplex.ιMapBifunctor K L (sheafTensor O) (up ℤ) (a + 1) b (n + 1)
            (by (try dsimp); omega) +
        a.negOnePow • (((sheafTensor O).obj (K.X a)).map (L.d b (b + 1)) ≫
          HomologicalComplex.ιMapBifunctor K L (sheafTensor O) (up ℤ) a (b + 1) (n + 1)
            (by (try dsimp); omega)) :=
  HomologicalComplex₂.ιTotal_d_up_ℤ _ a b n h

/-- **The sheaf-tensor pairing of complexes.**  Pair the coefficients in degrees `a` and `b`
with `sheafTensorPairing` and include into the totalization `Tot(K ⊗_{𝒪_X} L)` of the tensor
bicomplex. -/
noncomputable def sheafTensorComplexPairing :
    ComplexPairing.{u} (CoeffRing O V) ((sectionsComplexFunctor O V).obj K)
      ((sectionsComplexFunctor O V).obj L)
      ((sectionsComplexFunctor O V).obj
        (HomologicalComplex.mapBifunctor K L (sheafTensor O) (up ℤ))) where
  μ a b n h := sheafTensorPairing O V (K.X a) (L.X b) ≫
    (sectionsFunctor O V).map
      (HomologicalComplex.ιMapBifunctor K L (sheafTensor O) (up ℤ) a b n h)
  μ_d a b n h := by
    let : (sectionsFunctor O V).Additive :=
      Stacks.Cohomology.CechAcyclic.additive_sectionsPresheafFunctor (ringSheaf O) V
    have hd : ((sectionsComplexFunctor O V).obj
        (HomologicalComplex.mapBifunctor K L (sheafTensor O) (up ℤ))).d n (n + 1) =
        (sectionsFunctor O V).map
          ((HomologicalComplex.mapBifunctor K L (sheafTensor O) (up ℤ)).d n (n + 1)) := rfl
    rw [hd, Category.assoc, ← Functor.map_comp, ιMapBifunctor_d]
    simp only [Units.smul_def]
    rw [Functor.map_add, Functor.map_zsmul, Functor.map_comp, Functor.map_comp,
      Preadditive.comp_add, Preadditive.comp_zsmul, ← Category.assoc, ← Category.assoc,
      ← sheafTensorPairing_naturality_left O V (K.d a (a + 1)) (L.X b),
      ← sheafTensorPairing_naturality_right O V (K.X a) (L.d b (b + 1))]
    simp only [Category.assoc]
    rfl

/-! ### The cup product at these coefficients: the left column of Tag 0FKV -/

variable {ι : Type u} (U : ι → Opens X) (hU : V = ⨆ i, U i)

/-- **The Čech cup product at sheaf-tensor coefficients**: the signed Alexander--Whitney
cup-product map

`Tot(Tot(Č(𝒰,𝒦)) ⊗_A Tot(Č(𝒰,ℳ))) ⟶ Tot(Č(𝒰, Tot(𝒦 ⊗_{𝒪_X} ℳ)))`

for a covering `𝒰` of `V` and `A = 𝒪_X(V)`.  This is the left-hand column of the diagram of
Stacks Tag 0FKV: the source tensors the two total Čech complexes over the *ring* `A` of
sections on `V`, while in the target the coefficients are tensored over the *structure sheaf*,
the coefficient pairing being `sheafTensorComplexPairing`.

Its value on a homogeneous summand is the front/back restriction formula with the
Alexander--Whitney sign `cupProductSign n p r = (-1)^((p+r)n+rp+r)`: see
`Stacks.Cech.LinearCupProduct.cechCupProduct_ι`, which applies by
`Stacks.Cech.ModuleCupProduct.cechCupProductA_eq`. -/
@[stacks 07MB "the sheaf-tensor instantiation: source over the section ring, coefficients over
the structure sheaf"]
noncomputable def cechCupProductSheafTensor :
    HomologicalComplex.mapBifunctor ((totalCechComplexFunctorA O V U hU).obj K)
        ((totalCechComplexFunctorA O V U hU).obj L) (tensorModules (CoeffRing O V)) (up ℤ) ⟶
      (totalCechComplexFunctorA O V U hU).obj
        (HomologicalComplex.mapBifunctor K L (sheafTensor O) (up ℤ)) :=
  cechCupProductA O V U hU (sheafTensorComplexPairing O V K L)

/-- The cup product at sheaf-tensor coefficients is the `𝒪_X`-module cup product of
`Stacks.Cech.ModuleCupProduct` taken at the sheaf-tensor coefficient pairing. -/
theorem cechCupProductSheafTensor_eq :
    cechCupProductSheafTensor O V K L U hU =
      cechCupProductA O V U hU (sheafTensorComplexPairing O V K L) :=
  rfl

end Stacks.Cech.SheafTensorPairing

end
