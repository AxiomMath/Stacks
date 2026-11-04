module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.ModuleAlgebraData
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.AdicAlgebraLaws

/-!
# The tensor product sheaf as a monoidal product, and the algebra laws

The monoidal structure of [Stacks, Tag 01CA] on sheaves of modules over a scheme, and the
associativity and left unit laws of the multiplication of an algebra sheaf as morphisms of
sheaves of modules. The comparison of [Stacks, Tag 01CD] between inverse image and tensor product
intertwines the associator and the left unitor, so these laws are preserved by inverse image for a
multiplication that restricts to `AlgebraicGeometry.tensorDescentApp`.

## Main results

* `AlgebraicGeometry.tensorSheafMap_eq_tensorHom`: the induced map on a tensor product sheaf is
  the monoidal product of the two morphisms.
* `AlgebraicGeometry.multiplication_assoc`: the multiplication of an algebra sheaf is
  associative, as a morphism of sheaves of modules.
* `AlgebraicGeometry.unitModuleMap_comp_multiplication`: the structure morphism of an algebra
  sheaf is a left unit for its multiplication, as a morphism of sheaves of modules.
* `AlgebraicGeometry.schemePullbackTensorIso_associator` and
  `AlgebraicGeometry.schemePullbackTensorIso_leftUnitor`: the comparison of Tag 01CD intertwines
  the associator and the left unitor of Tag 01CA.
* `AlgebraicGeometry.map_assoc_of_tensorDescentApp` and
  `AlgebraicGeometry.map_one_of_tensorDescentApp`: the inverse image of a multiplication that
  restricts to `AlgebraicGeometry.tensorDescentApp` is associative, respectively unital.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory
open Stacks.RelativeSpec (AlgebraSheaf)
open Stacks.RelativeSpec.AlgebraSheaf (multiplication multiplication_tmul mulSection
  unitModuleMap unitModuleMap_apply structSection structSection_eq_smul_oneSection oneSection)
open Stacks.SheafOfModules.TensorStalkRingedSpace (tensorSheafMap_app_toTensorSheafSection
  toTensorSheafSection)
open Stacks.PullbackTensorCoherence (tmul tensor_hom_ext tensor_hom_ext₂ whiskerLeft_tmul
  whiskerRight_tmul tensorHom_tmul associator_hom_tmul leftUnitor_hom_tmul oneSec)
open Stacks.SheafOfModules (comp_val_app_apply)

universe u

namespace AlgebraicGeometry

/-- The monoidal structure of [Stacks, Tag 01CA] on sheaves of modules over a scheme, as an
instance on `AlgebraicGeometry.Scheme.Modules`: it is
`Stacks.PullbackGradedAlgebra.monoidalCategory X.toRingedSpace`. -/
@[instance_reducible]
local instance monoidalOfScheme (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Stacks.PullbackGradedAlgebra.monoidalCategory X.toRingedSpace

/-- The induced map on a tensor product sheaf sends a local pure tensor `x ⊗ y`, written with
`Stacks.PullbackTensorCoherence.tmul`, to the pure tensor `a x ⊗ b y`. -/
theorem tensorSheafMap_tmul {X : Scheme.{u}} {A A' B B' : X.Modules} (a : A ⟶ A') (b : B ⟶ B')
    (U : (X.Opens)ᵒᵖ) (x : A.val.obj U) (y : B.val.obj U) :
    (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩)).map
        ((a, b) : (_, _) ⟶ (_, _))).val.app U).hom (tmul X.toRingedSpace A B U x y) =
      tmul X.toRingedSpace A' B' U ((a.val.app U).hom x) ((b.val.app U).hom y) :=
  tensorSheafMap_app_toTensorSheafSection X.toRingedSpace A B A' B' a b U.unop x y

/-- The multiplication of an algebra sheaf sends a local pure tensor `x ⊗ y`, written with
`Stacks.PullbackTensorCoherence.tmul`, to the product of sections `mulSection C U x y`. -/
theorem multiplication_tmul' {W : Scheme.{u}} (C : AlgebraSheaf W) (U : (W.Opens)ᵒᵖ)
    (x y : (AlgebraSheaf.underlyingModule C).val.obj U) :
    ((multiplication C).val.app U).hom
        (tmul W.toRingedSpace (AlgebraSheaf.underlyingModule C)
          (AlgebraSheaf.underlyingModule C) U x y) = mulSection C U x y :=
  multiplication_tmul C U x y

/-- The induced map on a tensor product sheaf is the monoidal product `a ⊗ₘ b` of the two
morphisms. -/
theorem tensorSheafMap_eq_tensorHom {X : Scheme.{u}} {A A' B B' : X.Modules}
    (a : A ⟶ A') (b : B ⟶ B') :
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩)).map
      ((a, b) : (_, _) ⟶ (_, _))) = (a ⊗ₘ b : A ⊗ B ⟶ A' ⊗ B') :=
  tensor_hom_ext fun U x y => (tensorSheafMap_tmul a b U x y).trans (tensorHom_tmul a b U x y).symm

/-- The multiplication of an algebra sheaf is associative, as a morphism of sheaves of modules:
the two bracketings of the triple tensor product of the underlying module agree once the
associator of [Stacks, Tag 01CA] is inserted. -/
theorem multiplication_assoc {W : Scheme.{u}} (C : AlgebraSheaf W)
    (mul : (AlgebraSheaf.underlyingModule C ⊗ AlgebraSheaf.underlyingModule C : W.Modules) ⟶
      AlgebraSheaf.underlyingModule C)
    (hmul : mul = multiplication C) :
    (mul ▷ AlgebraSheaf.underlyingModule C) ≫ mul =
      (α_ (AlgebraSheaf.underlyingModule C) (AlgebraSheaf.underlyingModule C)
            (AlgebraSheaf.underlyingModule C)).hom ≫
        (AlgebraSheaf.underlyingModule C ◁ mul) ≫ mul := by
  subst hmul
  refine tensor_hom_ext₂ fun U a b c => ?_
  refine Eq.trans ((comp_val_app_apply _ _ U _).trans
    ((congrArg (fun z => ((multiplication C).val.app U).hom z)
        (whiskerRight_tmul (multiplication C) U
          (tmul W.toRingedSpace _ _ U a b) c)).trans
      ((congrArg (fun z => ((multiplication C).val.app U).hom
            (tmul W.toRingedSpace (AlgebraSheaf.underlyingModule C)
              (AlgebraSheaf.underlyingModule C) U z c))
          (multiplication_tmul' C U a b)).trans
        (multiplication_tmul' C U (mulSection C U a b) c)))) ?_
  have hassoc : ∀ x y z : C.right.obj.obj U,
      mulSection C U (mulSection C U x y) z = mulSection C U x (mulSection C U y z) :=
    fun x y z => mul_assoc x y z
  refine Eq.trans (hassoc a b c) ?_
  refine Eq.symm (((comp_val_app_apply _ _ U _).trans
    ((congrArg (fun z => ((((AlgebraSheaf.underlyingModule C ◁ multiplication C) ≫
            multiplication C)).val.app U).hom z)
        (associator_hom_tmul U a b c)).trans
      ((comp_val_app_apply _ _ U _).trans
        ((congrArg (fun z => ((multiplication C).val.app U).hom z)
            (whiskerLeft_tmul (multiplication C) U a
              (tmul W.toRingedSpace _ _ U b c))).trans
          ((congrArg (fun z => ((multiplication C).val.app U).hom
                (tmul W.toRingedSpace (AlgebraSheaf.underlyingModule C)
                  (AlgebraSheaf.underlyingModule C) U a z))
              (multiplication_tmul' C U b c)).trans
            (multiplication_tmul' C U a (mulSection C U b c))))))))

/-- The structure morphism of an algebra sheaf is a left unit for its multiplication, as a
morphism of sheaves of modules: `(u ▷ C) ≫ mul` is the left unitor of [Stacks, Tag 01CA]. -/
theorem unitModuleMap_comp_multiplication {W : Scheme.{u}} (C : AlgebraSheaf W)
    (mul : (AlgebraSheaf.underlyingModule C ⊗ AlgebraSheaf.underlyingModule C : W.Modules) ⟶
      AlgebraSheaf.underlyingModule C)
    (hmul : mul = multiplication C)
    (u : (𝟙_ W.Modules) ⟶ AlgebraSheaf.underlyingModule C) (hu : u = unitModuleMap C) :
    (u ▷ AlgebraSheaf.underlyingModule C) ≫ mul =
      (λ_ (AlgebraSheaf.underlyingModule C)).hom := by
  subst hmul
  subst hu
  refine tensor_hom_ext fun U r x => ?_
  refine Eq.trans ?_ (leftUnitor_hom_tmul U r x).symm
  exact (comp_val_app_apply _ _ U _).trans
    ((congrArg (fun z => ((multiplication C).val.app U).hom z)
          (whiskerRight_tmul (unitModuleMap C) U r x)).trans
      (multiplication_tmul' C U _ x))

/-! ### The associativity of a conjugated multiplication, and its transport along the comparison -/

/-- A multiplication conjugated by a retraction is associative: for `ε : V ⟶ M`, `δ : M ⟶ V`
with `δ ≫ ε = 𝟙 M` and an associative `mul` on `M`, the composite `(ε ⊗ ε) ≫ mul ≫ δ` is an
associative multiplication on `V`. -/
private theorem conjAssoc {C : Type*} [Category C] [MonoidalCategory C] {V M : C}
    (ε : V ⟶ M) (δ : M ⟶ V) (hδε : δ ≫ ε = 𝟙 M) (mul : M ⊗ M ⟶ M)
    (hassoc : (mul ▷ M) ≫ mul = (α_ M M M).hom ≫ (M ◁ mul) ≫ mul) :
    ((((ε ⊗ₘ ε) ≫ mul ≫ δ) ▷ V)) ≫ ((ε ⊗ₘ ε) ≫ mul ≫ δ) =
      (α_ V V V).hom ≫ (V ◁ ((ε ⊗ₘ ε) ≫ mul ≫ δ)) ≫ ((ε ⊗ₘ ε) ≫ mul ≫ δ) := by
  have hYε : ((ε ⊗ₘ ε) ≫ mul ≫ δ) ≫ ε = (ε ⊗ₘ ε) ≫ mul := by
    rw [Category.assoc, Category.assoc, hδε, Category.comp_id]
  have hL : ((((ε ⊗ₘ ε) ≫ mul ≫ δ) ▷ V)) ≫ ((ε ⊗ₘ ε) ≫ mul ≫ δ) =
      (((ε ⊗ₘ ε) ⊗ₘ ε) ≫ (mul ▷ M)) ≫ mul ≫ δ := by
    rw [← MonoidalCategory.tensorHom_id ((ε ⊗ₘ ε) ≫ mul ≫ δ) V,
      ← MonoidalCategory.tensorHom_id mul M, ← Category.assoc,
      MonoidalCategory.tensorHom_comp_tensorHom, MonoidalCategory.tensorHom_comp_tensorHom,
      hYε, Category.id_comp, Category.comp_id]
  have hR : (V ◁ ((ε ⊗ₘ ε) ≫ mul ≫ δ)) ≫ ((ε ⊗ₘ ε) ≫ mul ≫ δ) =
      ((ε ⊗ₘ (ε ⊗ₘ ε)) ≫ (M ◁ mul)) ≫ mul ≫ δ := by
    rw [← MonoidalCategory.id_tensorHom V ((ε ⊗ₘ ε) ≫ mul ≫ δ),
      ← MonoidalCategory.id_tensorHom M mul, ← Category.assoc,
      MonoidalCategory.tensorHom_comp_tensorHom, MonoidalCategory.tensorHom_comp_tensorHom,
      hYε, Category.id_comp, Category.comp_id]
  rw [hL, hR]
  simp only [Category.assoc]
  rw [← Category.assoc (mul ▷ M) mul δ, hassoc]
  simp only [Category.assoc]
  rw [MonoidalCategory.associator_naturality_assoc]

/-- The transport of an associativity law along a comparison of tensor products, in a monoidal
category: `h1` and `h2` are the naturality of the comparison in each variable and `h3` its
compatibility with the associator; if `pμ = c ≫ (ε ⊗ ε) ≫ mul ≫ δ` with `δ ≫ ε = 𝟙 M` and `mul`
associative, then `pw ≫ pμ = pa ≫ pl ≫ pμ`. -/
private theorem assocDescentChain {C : Type*} [Category C] [MonoidalCategory C]
    {T₂ T₃ S V M : C} {pμ : S ⟶ V} {pw : T₂ ⟶ S} {pa : T₂ ⟶ T₃} {pl : T₃ ⟶ S}
    {c : S ⟶ V ⊗ V} {c₂ : T₂ ⟶ S ⊗ V} {c₃ : T₃ ⟶ V ⊗ S}
    {ε : V ⟶ M} {δ : M ⟶ V} {mul : M ⊗ M ⟶ M}
    (h1 : pw ≫ c = c₂ ≫ (pμ ▷ V))
    (h2 : pl ≫ c = c₃ ≫ (V ◁ pμ))
    (h3 : pa ≫ c₃ ≫ (V ◁ c) = c₂ ≫ (c ▷ V) ≫ (α_ V V V).hom)
    (hμ : pμ = c ≫ (ε ⊗ₘ ε) ≫ mul ≫ δ)
    (hδε : δ ≫ ε = 𝟙 M)
    (hassoc : (mul ▷ M) ≫ mul = (α_ M M M).hom ≫ (M ◁ mul) ≫ mul) :
    pw ≫ pμ = pa ≫ pl ≫ pμ := by
  calc pw ≫ pμ
      = (pw ≫ c) ≫ ((ε ⊗ₘ ε) ≫ mul ≫ δ) := by
        rw [hμ]; simp only [Category.assoc]
    _ = c₂ ≫ (pμ ▷ V) ≫ ((ε ⊗ₘ ε) ≫ mul ≫ δ) := by rw [h1]; simp only [Category.assoc]
    _ = c₂ ≫ (c ▷ V) ≫ ((((ε ⊗ₘ ε) ≫ mul ≫ δ) ▷ V)) ≫ ((ε ⊗ₘ ε) ≫ mul ≫ δ) := by
        rw [hμ]
        simp only [MonoidalCategory.comp_whiskerRight, Category.assoc]
    _ = c₂ ≫ (c ▷ V) ≫ (α_ V V V).hom ≫ (V ◁ ((ε ⊗ₘ ε) ≫ mul ≫ δ)) ≫
          ((ε ⊗ₘ ε) ≫ mul ≫ δ) := by rw [conjAssoc ε δ hδε mul hassoc]
    _ = (pa ≫ c₃ ≫ (V ◁ c)) ≫ (V ◁ ((ε ⊗ₘ ε) ≫ mul ≫ δ)) ≫ ((ε ⊗ₘ ε) ≫ mul ≫ δ) := by
        rw [h3]; simp only [Category.assoc]
    _ = pa ≫ c₃ ≫ (V ◁ pμ) ≫ ((ε ⊗ₘ ε) ≫ mul ≫ δ) := by
        rw [hμ]; simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
    _ = pa ≫ (pl ≫ c) ≫ ((ε ⊗ₘ ε) ≫ mul ≫ δ) := by rw [h2]; simp only [Category.assoc]
    _ = pa ≫ pl ≫ pμ := by rw [hμ]; simp only [Category.assoc]


/-! ### The three coherences of the comparison, at the spelling of the adic development -/

/-- The comparison `Stacks.Tag01VSPullbackTensor.schemePullbackTensorIso` of
[Stacks, Tag 01CD] is natural in the first variable, in whiskered form. -/
public theorem schemePullbackTensorIso_whiskerRight {X Y : Scheme.{u}} (g : X ⟶ Y)
    {A A' : Y.Modules} (u : A ⟶ A') (B : Y.Modules) :
    (Scheme.Modules.pullback g).map (u ▷ B) ≫
        (Stacks.Tag01VSPullbackTensor.schemePullbackTensorIso g A' B).hom =
      (Stacks.Tag01VSPullbackTensor.schemePullbackTensorIso g A B).hom ≫
        ((Scheme.Modules.pullback g).map u ▷ (Scheme.Modules.pullback g).obj B) :=
  Stacks.PullbackTensorCoherence.pullbackTensorComparison_naturality_left g.toLRSHom.toShHom u

/-- The comparison `Stacks.Tag01VSPullbackTensor.schemePullbackTensorIso` of
[Stacks, Tag 01CD] is natural in the second variable, in whiskered form. -/
public theorem schemePullbackTensorIso_whiskerLeft {X Y : Scheme.{u}} (g : X ⟶ Y)
    (A : Y.Modules) {B B' : Y.Modules} (v : B ⟶ B') :
    (Scheme.Modules.pullback g).map (A ◁ v) ≫
        (Stacks.Tag01VSPullbackTensor.schemePullbackTensorIso g A B').hom =
      (Stacks.Tag01VSPullbackTensor.schemePullbackTensorIso g A B).hom ≫
        ((Scheme.Modules.pullback g).obj A ◁ (Scheme.Modules.pullback g).map v) :=
  Stacks.PullbackTensorCoherence.pullbackTensorComparison_naturality_right g.toLRSHom.toShHom v

/-- The comparison of [Stacks, Tag 01CD] intertwines the associator of [Stacks, Tag 01CA]:
splitting the inverse image of a triple tensor product and then rebracketing is rebracketing
first and then splitting. -/
public theorem schemePullbackTensorIso_associator {X Y : Scheme.{u}} (g : X ⟶ Y)
    (A B D : Y.Modules) :
    (Scheme.Modules.pullback g).map (α_ A B D).hom ≫
        (Stacks.Tag01VSPullbackTensor.schemePullbackTensorIso g A (B ⊗ D)).hom ≫
          ((Scheme.Modules.pullback g).obj A ◁
            (Stacks.Tag01VSPullbackTensor.schemePullbackTensorIso g B D).hom) =
      (Stacks.Tag01VSPullbackTensor.schemePullbackTensorIso g (A ⊗ B) D).hom ≫
        ((Stacks.Tag01VSPullbackTensor.schemePullbackTensorIso g A B).hom ▷
            (Scheme.Modules.pullback g).obj D) ≫
          (α_ ((Scheme.Modules.pullback g).obj A) ((Scheme.Modules.pullback g).obj B)
            ((Scheme.Modules.pullback g).obj D)).hom :=
  Stacks.PullbackTensorCoherence.pullbackTensorComparison_associator g.toLRSHom.toShHom A B D

/-! ### The associativity of the descended multiplication, on a thickening -/

/-- If the inverse image of `μ` is `AlgebraicGeometry.tensorDescentApp w N M ε δ mul`, it is the
comparison of [Stacks, Tag 01CD] followed by `(ε ⊗ₘ ε) ≫ mul ≫ δ`. -/
private theorem map_eq_comparison_of_tensorDescentApp {W W'' : Scheme.{u}} (w : W ⟶ W'')
    (N : W''.Modules) (μ : (N ⊗ N : W''.Modules) ⟶ N) {M : W.Modules}
    (ε : (Scheme.Modules.pullback w).obj N ⟶ M) (δ : M ⟶ (Scheme.Modules.pullback w).obj N)
    (mul : (M ⊗ M : W.Modules) ⟶ M)
    (hμ : (Scheme.Modules.pullback w).map μ = tensorDescentApp w N M ε δ mul) :
    (Scheme.Modules.pullback w).map μ =
      (Stacks.Tag01VSPullbackTensor.schemePullbackTensorIso w N N).hom ≫
        (ε ⊗ₘ ε) ≫ mul ≫ δ :=
  hμ.trans ((tensorDescentApp_eq w N M ε δ mul).trans
    (congrArg
      (fun z => (Stacks.Tag01VSPullbackTensor.schemePullbackTensorIso w N N).hom ≫
        z ≫ mul ≫ δ)
      (tensorSheafMap_eq_tensorHom ε ε)))

/-- For `w : W ⟶ W''` and a multiplication `μ` on a module `N` over `W''` whose inverse image
along `w` is `AlgebraicGeometry.tensorDescentApp w N M ε δ mul`, the inverse images of the two
bracketings of `μ` agree as soon as `mul` is associative and `δ ≫ ε = 𝟙 M`. -/
public theorem map_assoc_of_tensorDescentApp {W W'' : Scheme.{u}} (w : W ⟶ W'')
    (N : W''.Modules) (μ : (N ⊗ N : W''.Modules) ⟶ N) {M : W.Modules}
    (ε : (Scheme.Modules.pullback w).obj N ⟶ M) (δ : M ⟶ (Scheme.Modules.pullback w).obj N)
    (hδε : δ ≫ ε = 𝟙 M) (mul : (M ⊗ M : W.Modules) ⟶ M)
    (hassoc : (mul ▷ M) ≫ mul = (α_ M M M).hom ≫ (M ◁ mul) ≫ mul)
    (hμ : (Scheme.Modules.pullback w).map μ = tensorDescentApp w N M ε δ mul) :
    (Scheme.Modules.pullback w).map ((μ ▷ N) ≫ μ) =
      (Scheme.Modules.pullback w).map ((α_ N N N).hom ≫ (N ◁ μ) ≫ μ) := by
  have hμ' := map_eq_comparison_of_tensorDescentApp w N μ ε δ mul hμ
  refine ((Scheme.Modules.pullback w).map_comp (μ ▷ N) μ).trans
    ((assocDescentChain (schemePullbackTensorIso_whiskerRight w μ N)
        (schemePullbackTensorIso_whiskerLeft w N μ) (schemePullbackTensorIso_associator w N N N)
        hμ' hδε hassoc).trans ?_)
  exact (((Scheme.Modules.pullback w).map_comp (α_ N N N).hom ((N ◁ μ) ≫ μ)).trans
    (congrArg (fun z => (Scheme.Modules.pullback w).map (α_ N N N).hom ≫ z)
      ((Scheme.Modules.pullback w).map_comp (N ◁ μ) μ))).symm

/-! ### The left unitor crossing and the unit law on a thickening -/

/-- The comparison of [Stacks, Tag 01CD] intertwines the left unitor of [Stacks, Tag 01CA], the
unit object being matched by `Stacks.AlgebraicGeometry.AffineBaseChange.pullbackUnitIso`. -/
public theorem schemePullbackTensorIso_leftUnitor {X Y : Scheme.{u}} (g : X ⟶ Y)
    (A : Y.Modules) :
    (Scheme.Modules.pullback g).map (λ_ A).hom =
      (Stacks.Tag01VSPullbackTensor.schemePullbackTensorIso g (𝟙_ Y.Modules) A).hom ≫
        ((Stacks.AlgebraicGeometry.AffineBaseChange.pullbackUnitIso g).hom ▷
            (Scheme.Modules.pullback g).obj A) ≫
          (λ_ ((Scheme.Modules.pullback g).obj A)).hom :=
  Stacks.PullbackTensorCoherence.pullbackTensorComparison_leftUnitor g.toLRSHom.toShHom A

/-- The transport of a left unit law along a comparison of tensor products, in a monoidal
category: if `pμ = c ≫ (ε ⊗ ε) ≫ mul ≫ δ` and `pη = uc ≫ u ≫ δ` with `ε`, `δ` mutually inverse
and `u` a left unit for `mul`, then `pli ≫ pn ≫ pμ = 𝟙 V`. -/
private theorem unitDescentChain {C : Type*} [Category C] [MonoidalCategory C]
    {W₁ S V M Z : C} {pli : V ⟶ W₁} {plh : W₁ ⟶ V} {pn : W₁ ⟶ S} {pμ : S ⟶ V}
    {pη : Z ⟶ V} {uc : Z ⟶ 𝟙_ C} {c₁ : W₁ ⟶ Z ⊗ V} {c : S ⟶ V ⊗ V}
    {ε : V ⟶ M} {δ : M ⟶ V} {u : 𝟙_ C ⟶ M} {mul : M ⊗ M ⟶ M}
    (hunitor : plh = c₁ ≫ (uc ▷ V) ≫ (λ_ V).hom)
    (hli : pli ≫ plh = 𝟙 V)
    (hn : pn ≫ c = c₁ ≫ (pη ▷ V))
    (hμ : pμ = c ≫ (ε ⊗ₘ ε) ≫ mul ≫ δ)
    (hη : pη = uc ≫ u ≫ δ)
    (hδε : δ ≫ ε = 𝟙 M) (hεδ : ε ≫ δ = 𝟙 V)
    (hone : (u ▷ M) ≫ mul = (λ_ M).hom) :
    pli ≫ pn ≫ pμ = 𝟙 V := by
  have h1 : (δ ▷ V) ≫ (ε ⊗ₘ ε) = M ◁ ε := by
    rw [← MonoidalCategory.tensorHom_id δ V, MonoidalCategory.tensorHom_comp_tensorHom, hδε,
      Category.id_comp, MonoidalCategory.id_tensorHom]
  calc pli ≫ pn ≫ pμ
      = pli ≫ (pn ≫ c) ≫ ((ε ⊗ₘ ε) ≫ mul ≫ δ) := by simp only [hμ, Category.assoc]
    _ = pli ≫ c₁ ≫ (pη ▷ V) ≫ ((ε ⊗ₘ ε) ≫ mul ≫ δ) := by rw [hn]; simp only [Category.assoc]
    _ = pli ≫ c₁ ≫ (uc ▷ V) ≫ (u ▷ V) ≫ (δ ▷ V) ≫ ((ε ⊗ₘ ε) ≫ mul ≫ δ) := by
        simp only [hη, MonoidalCategory.comp_whiskerRight, Category.assoc]
    _ = pli ≫ c₁ ≫ (uc ▷ V) ≫ (λ_ V).hom := by
        rw [reassoc_of% h1, ← MonoidalCategory.whisker_exchange_assoc, reassoc_of% hone,
          MonoidalCategory.leftUnitor_naturality_assoc, hεδ, Category.comp_id]
    _ = pli ≫ plh := by rw [hunitor]
    _ = 𝟙 V := hli

/-- For `w : W ⟶ W''`, a multiplication `μ` and a unit `η` on a module `N` over `W''` whose
inverse images along `w` are `AlgebraicGeometry.tensorDescentApp w N M ε δ mul` and the unit `u`
of `M` read through `δ`, the endomorphism `λ⁻¹ ≫ (η ▷ N) ≫ μ` pulls back to the identity, as soon
as `u` is a left unit for `mul` and `ε`, `δ` are mutually inverse. -/
public theorem map_one_of_tensorDescentApp {W W'' : Scheme.{u}} (w : W ⟶ W'')
    (N : W''.Modules) (μ : (N ⊗ N : W''.Modules) ⟶ N) (η : (𝟙_ W''.Modules) ⟶ N)
    {M : W.Modules} (ε : (Scheme.Modules.pullback w).obj N ⟶ M)
    (δ : M ⟶ (Scheme.Modules.pullback w).obj N) (hδε : δ ≫ ε = 𝟙 M)
    (hεδ : ε ≫ δ = 𝟙 ((Scheme.Modules.pullback w).obj N))
    (mul : (M ⊗ M : W.Modules) ⟶ M) (u : (𝟙_ W.Modules) ⟶ M)
    (hone : (u ▷ M) ≫ mul = (λ_ M).hom)
    (hμ : (Scheme.Modules.pullback w).map μ = tensorDescentApp w N M ε δ mul)
    (hη : (Stacks.AlgebraicGeometry.AffineBaseChange.pullbackUnitIso w).inv ≫
      (Scheme.Modules.pullback w).map η = u ≫ δ) :
    (Scheme.Modules.pullback w).map ((λ_ N).inv ≫ (η ▷ N) ≫ μ) =
      𝟙 ((Scheme.Modules.pullback w).obj N) := by
  have hμ' := map_eq_comparison_of_tensorDescentApp w N μ ε δ mul hμ
  have hli : (Scheme.Modules.pullback w).map (λ_ N).inv ≫
      (Scheme.Modules.pullback w).map (λ_ N).hom =
        𝟙 ((Scheme.Modules.pullback w).obj N) :=
    ((Scheme.Modules.pullback w).map_comp (λ_ N).inv (λ_ N).hom).symm.trans
      ((congrArg (Scheme.Modules.pullback w).map (λ_ N).inv_hom_id).trans
        ((Scheme.Modules.pullback w).map_id N))
  have hη' : (Scheme.Modules.pullback w).map η =
      (Stacks.AlgebraicGeometry.AffineBaseChange.pullbackUnitIso w).hom ≫ u ≫ δ :=
    (Iso.inv_comp_eq (Stacks.AlgebraicGeometry.AffineBaseChange.pullbackUnitIso w)).mp hη
  refine Eq.trans ?_ (unitDescentChain (schemePullbackTensorIso_leftUnitor w N) hli
    (schemePullbackTensorIso_whiskerRight w η N) hμ' hη' hδε hεδ hone)
  exact ((Scheme.Modules.pullback w).map_comp (λ_ N).inv ((η ▷ N) ≫ μ)).trans
    (congrArg (fun z => (Scheme.Modules.pullback w).map (λ_ N).inv ≫ z)
      ((Scheme.Modules.pullback w).map_comp (η ▷ N) μ))

end AlgebraicGeometry

end
