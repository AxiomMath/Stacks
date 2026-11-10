module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedToposPushforwardRestrictCoeff

/-!
# The direct image along a morphism of ringed topoi through the inverse image of the base

Let `f : (Sh(C'), O') ⟶ (Sh(C), O)` be a morphism of ringed topoi, let
`g : (Sh(C'), f⁻¹O) ⟶ (Sh(C), O)` be `f` with the identity of `f⁻¹O` as structure map, and let
`α : f⁻¹O ⟶ O'` be the inverse-image form of the structure map of `f`. On sheaves of modules the
direct image along `f` is restriction of scalars along `α` followed by the direct image along
`g`, on the nose on underlying sheaves, and the two tensorators agree on pure tensors of local
sections (`SheafOfModules.DifferentialGradedModule.toposDirectImageModules_μ_comp_map_app`). This
file lifts that identification to differential graded algebras and modules: for a sheaf of
differential graded `O'`-algebras `B`,

* `f_*B` and `g_*B♭` are the same sheaf of differential graded `O`-algebras
  (`directImageRestrictCoeffAlgebraHom`), `B♭` being the restriction of scalars of `B` along `α`;
* for a unital `ψ : A ⟶ f_*B`, the direct image of right differential graded `B`-modules along
  `(f, ψ)` is restriction of scalars to `B♭` followed by the direct image along `(g, ψ')`, where
  `ψ'` is `ψ` read into `g_*B♭` (`toposPushforwardRestrictCoeffIso`).

All the comparison maps are the identity on local sections.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.TensoratorCompatible`: for lax monoidal functors
  `G₁` and `G₂` and an isomorphism `c : G₁ ≅ restrictCoeffSheaf α ⋙ G₂`, the tensorators agree
  through `c` on pure tensors; `TensoratorCompatible.algebraHom`,
  `TensoratorCompatible.structureMap` and `TensoratorCompatible.pushforwardIso` are the
  differential graded consequences, in this generality.
* `SheafOfModules.DifferentialGradedModule.directImageRestrictCoeffIso`: the identity
  `f_* ≅ restrictCoeffSheaf α ⋙ g_*` of functors on sheaves of modules.
* `SheafOfModules.DifferentialGradedModule.directImageRestrictCoeffAlgebraHom`: the identity
  `f_*B ⟶ g_*B♭` of sheaves of differential graded algebras.
* `SheafOfModules.DifferentialGradedModule.restrictCoeffStructureMap`: `ψ' : A ⟶ g_*B♭`.
* `SheafOfModules.DifferentialGradedModule.toposPushforwardRestrictCoeffIso`:
  `f_{*,ψ} ≅ restrictCoeffFunctor α ⋙ g_{*,ψ'}`.

## Implementation notes

The direct image along `g` is typed over the site of `(Sh(C'), f⁻¹O)`, which is the site of `X`
only after unfolding `inverseImageRingedTopos`, while restriction of scalars along `α` lands in
sheaves of modules spelled over the site of `X`. Unifying two elaborated terms which differ only
in this spelling of their implicit category and monoidal arguments times out, so every
instantiation of the generic statements at `g` passes the lax monoidal structure
`toposDirectImageModules_laxMonoidal (inverseImageRingedToposHom f)` explicitly, and the one
comparison with `toposDirectImageModules_μ_comp_map_app` is made against a statement elaborated
in the same way.

## References

* [Stacks Project, Tag 0FSI](https://stacks.math.columbia.edu/tag/0FSI)
-/

@[expose] public section

open CategoryTheory MonoidalCategory CategoryTheory.Sheaf
open Stacks.Sheaves.RingedToposModules Stacks.Sheaves.RingedToposModules.RingedToposHom
open scoped TensorProduct

universe w v₁ u₁ v₂ u₂

namespace SheafOfModules.DifferentialGradedModule

section Comparison

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  {R R' : Sheaf J CommRingCat.{w}} (α : toRingCat J R ⟶ toRingCat J R')
  {D : Type u₂} [Category.{v₂} D] {K : GrothendieckTopology D}
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] {S : Sheaf K CommRingCat.{w}}
  [K.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify K AddCommGrpCat.{w}]

attribute [local instance] Stacks.TensorSheafWorld.monoidalCategory

variable (G₁ : SheafOfModules.{w} (toRingCat J R') ⥤ SheafOfModules.{w} (toRingCat K S))
  [iG₁ : G₁.LaxMonoidal] [G₁.Additive]
  (G₂ : SheafOfModules.{w} (toRingCat J R) ⥤ SheafOfModules.{w} (toRingCat K S))
  [iG₂ : G₂.LaxMonoidal] [G₂.Additive]
  (c : G₁ ≅ restrictCoeffSheaf α ⋙ G₂)

/-- **The tensorators of `G₁` and `G₂` agree through `c`**: for morphisms `m : M ⊗ N ⟶ P` of
sheaves of `R'`-modules and `m' : M♭ ⊗ N♭ ⟶ P♭` of sheaves of `R`-modules which agree on pure
tensors of local sections, the tensorator of `G₁` followed by `G₁m` and by `c` agrees on pure
tensors with `c ⊗ c` followed by the tensorator of `G₂`, by `G₂m'` and by `c⁻¹`. -/
def TensoratorCompatible : Prop :=
  ∀ {M N P : SheafOfModules.{w} (toRingCat J R')} (m : M ⊗ N ⟶ P)
    (m' : (restrictCoeffSheaf α).obj M ⊗ (restrictCoeffSheaf α).obj N ⟶
      (restrictCoeffSheaf α).obj P),
    (∀ (U : Cᵒᵖ) (a : ((restrictCoeffSheaf α).obj M).val.obj U)
        (b : ((restrictCoeffSheaf α).obj N).val.obj U),
      m.val.app U ((PresheafOfModules.tensorSheafUnit M N).app U
          ((show M.val.obj U from a) ⊗ₜ (show N.val.obj U from b))) =
        m'.val.app U ((PresheafOfModules.tensorSheafUnit ((restrictCoeffSheaf α).obj M)
          ((restrictCoeffSheaf α).obj N)).app U (a ⊗ₜ b))) →
    ∀ (V : Dᵒᵖ) (x : (G₁.obj M).val.obj V) (y : (G₁.obj N).val.obj V),
      (Functor.LaxMonoidal.μ G₁ M N ≫ G₁.map m).val.app V
          ((PresheafOfModules.tensorSheafUnit (G₁.obj M) (G₁.obj N)).app V (x ⊗ₜ y)) =
        (c.inv.app P).val.app V
          ((Functor.LaxMonoidal.μ G₂ ((restrictCoeffSheaf α).obj M)
              ((restrictCoeffSheaf α).obj N) ≫ G₂.map m').val.app V
            ((PresheafOfModules.tensorSheafUnit (G₂.obj ((restrictCoeffSheaf α).obj M))
              (G₂.obj ((restrictCoeffSheaf α).obj N))).app V
              ((c.hom.app M).val.app V x ⊗ₜ (c.hom.app N).val.app V y)))

variable {α G₁ G₂ c}

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify K AddCommGrpCat.{w}]
  iG₁ [G₁.Additive] iG₂ [G₂.Additive] in
/-- `c` followed by its inverse is the identity on local sections. -/
theorem hom_inv_val_app (M : SheafOfModules.{w} (toRingCat J R')) (U : Dᵒᵖ)
    (x : (G₁.obj M).val.obj U) :
    (c.inv.app M).val.app U ((c.hom.app M).val.app U x) = x :=
  congrArg (fun φ : G₁.obj M ⟶ G₁.obj M => φ.val.app U x) (c.hom_inv_id_app M)

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify K AddCommGrpCat.{w}]
  iG₁ [G₁.Additive] iG₂ [G₂.Additive] in
/-- The inverse of `c` followed by `c` is the identity on local sections. -/
theorem inv_hom_val_app (M : SheafOfModules.{w} (toRingCat J R')) (U : Dᵒᵖ)
    (x : (G₂.obj ((restrictCoeffSheaf α).obj M)).val.obj U) :
    (c.hom.app M).val.app U ((c.inv.app M).val.app U x) = x :=
  congrArg (fun φ : G₂.obj ((restrictCoeffSheaf α).obj M) ⟶ G₂.obj ((restrictCoeffSheaf α).obj M) =>
    φ.val.app U x) (c.inv_hom_id_app M)

variable (hc : TensoratorCompatible α G₁ G₂ c)
  (B : DifferentialGradedAlgebra.{w, w} (toRingCat J R'))

include hc in
/-- `c` is multiplicative from `G₁B` to `G₂B♭`. -/
theorem TensoratorCompatible.map_mul (n m : ℤ) (U : Dᵒᵖ)
    (x : ((toposPushforwardAlgebra G₁ B).complex.X n).val.obj U)
    (y : ((toposPushforwardAlgebra G₁ B).complex.X m).val.obj U) :
    (c.hom.app (B.complex.X (n + m))).val.app U
        (((toposPushforwardAlgebra G₁ B).mul n m).app U x y) =
      ((toposPushforwardAlgebra G₂ (B.restrictCoeff α)).mul n m).app U
        ((c.hom.app (B.complex.X n)).val.app U x) ((c.hom.app (B.complex.X m)).val.app U y) :=
  (congrArg (fun z => (c.hom.app (B.complex.X (n + m))).val.app U z)
    (hc (GradedAlgebra.mulSheaf B.toGradedAlgebra n m)
      (GradedAlgebra.mulSheaf (B.restrictCoeff α).toGradedAlgebra n m)
      (fun U a b => (GradedAlgebra.mulSheaf_unit B.toGradedAlgebra n m U a b).trans
        (GradedAlgebra.mulSheaf_unit (B.restrictCoeff α).toGradedAlgebra n m U a b).symm)
      U x y)).trans (inv_hom_val_app (c := c) _ U _)

/-- **`G₁B` is `G₂B♭`**: the components of `c` form a homomorphism of sheaves of differential
graded algebras from the image of `B` under `G₁` to the image under `G₂` of its restriction of
scalars. -/
noncomputable def TensoratorCompatible.algebraHom :
    toposPushforwardAlgebra G₁ B ⟶ toposPushforwardAlgebra G₂ (B.restrictCoeff α) where
  toHomologicalComplex :=
    { f n := c.hom.app (B.complex.X n)
      comm' i j _ := (c.hom.naturality (B.complex.d i j)).symm }
  map_mul n m U x y := hc.map_mul B n m U x y

/-- The components of `G₁B ⟶ G₂B♭` are those of `c`. -/
theorem TensoratorCompatible.algebraHom_f (n : ℤ) :
    (hc.algebraHom B).toHomologicalComplex.f n = c.hom.app (B.complex.X n) :=
  rfl

/-- **`G₁B ⟶ G₂B♭` is unital.** A multiplicative bijection on local sections carries the unit to
the unit: `c 1 = c 1 · 1 = c 1 · c (c⁻¹ 1) = c (1 · c⁻¹ 1) = c (c⁻¹ 1) = 1`. -/
theorem TensoratorCompatible.isUnital_algebraHom : (hc.algebraHom B).IsUnital := by
  intro U
  let one₁ := (toposPushforwardAlgebra G₁ B).one.eval U
  let one₂ := (toposPushforwardAlgebra G₂ (B.restrictCoeff α)).one.eval U
  let b : ((toposPushforwardAlgebra G₁ B).complex.X 0).val.obj U :=
    (c.inv.app (B.complex.X 0)).val.app U one₂
  have hb : (c.hom.app (B.complex.X 0)).val.app U b = one₂ :=
    inv_hom_val_app (c := c) (B.complex.X 0) U one₂
  have h1 : ((toposPushforwardAlgebra G₂ (B.restrictCoeff α)).mul 0 0).app U
      ((c.hom.app (B.complex.X 0)).val.app U one₁) one₂ =
        (c.hom.app (B.complex.X 0)).val.app U one₁ :=
    eq_of_heq ((toposPushforwardAlgebra G₂ (B.restrictCoeff α)).mul_one 0 U
      ((c.hom.app (B.complex.X 0)).val.app U one₁))
  have h3 : ((toposPushforwardAlgebra G₁ B).mul 0 0).app U one₁ b = b :=
    eq_of_heq ((toposPushforwardAlgebra G₁ B).one_mul 0 U b)
  have h2 := hc.map_mul B 0 0 U one₁ b
  change (c.hom.app (B.complex.X 0)).val.app U one₁ = one₂
  refine h1.symm.trans ?_
  refine (congrArg (fun z => ((toposPushforwardAlgebra G₂ (B.restrictCoeff α)).mul 0 0).app U
    ((c.hom.app (B.complex.X 0)).val.app U one₁) z) hb.symm).trans ?_
  refine h2.symm.trans ?_
  refine (congrArg (fun z => (c.hom.app (B.complex.X 0)).val.app U z) h3).trans ?_
  exact hb

/-! ### Direct images of differential graded modules -/

variable {B} {A : DifferentialGradedAlgebra.{w, w} (toRingCat K S)}
  (ψ : A ⟶ toposPushforwardAlgebra G₁ B) (hψ : ψ.IsUnital)

/-- **`ψ` read into `G₂B♭`**: the structure homomorphism `ψ` followed by `G₁B ⟶ G₂B♭`. -/
noncomputable abbrev TensoratorCompatible.structureMap :
    A ⟶ toposPushforwardAlgebra G₂ (B.restrictCoeff α) :=
  ψ ≫ hc.algebraHom B

include hψ in
/-- The structure homomorphism read into `G₂B♭` is unital. -/
theorem TensoratorCompatible.isUnital_structureMap : (hc.structureMap ψ).IsUnital := fun U =>
  (congrArg (fun z => (c.hom.app (B.complex.X 0)).val.app U z) (hψ U)).trans
    (hc.isUnital_algebraHom B U)

/-- `c` intertwines the actions of `A` on the two direct images. -/
theorem TensoratorCompatible.module_map_mul (Q : DifferentialGradedModule.{w, w, w} B)
    (n i : ℤ) (U : Dᵒᵖ) (x : (((toposPushforward G₁ ψ hψ).obj Q).complex.X n).val.obj U)
    (y : (A.complex.X i).val.obj U) :
    (c.hom.app (Q.complex.X (n + i))).val.app U
        ((((toposPushforward G₁ ψ hψ).obj Q).mul n i).app U x y) =
      (((toposPushforward G₂ (hc.structureMap ψ) (hc.isUnital_structureMap ψ hψ)).obj
          ((restrictCoeffFunctor α).obj Q)).mul n i).app U
        ((c.hom.app (Q.complex.X n)).val.app U x) y :=
  (congrArg (fun z => (c.hom.app (Q.complex.X (n + i))).val.app U z)
    (hc (smulSheaf Q n i) (smulSheaf ((restrictCoeffFunctor α).obj Q) n i)
      (fun U a b => (smulSheaf_unit Q n i U a b).trans
        (smulSheaf_unit ((restrictCoeffFunctor α).obj Q) n i U a b).symm)
      U x ((ψ.toHomologicalComplex.f i).val.app U y))).trans (inv_hom_val_app (c := c) _ U _)

/-- The components of `c` as a homomorphism of right differential graded `A`-modules. -/
noncomputable def TensoratorCompatible.moduleHom (Q : DifferentialGradedModule.{w, w, w} B) :
    (toposPushforward G₁ ψ hψ).obj Q ⟶
      (restrictCoeffFunctor α ⋙
        toposPushforward G₂ (hc.structureMap ψ) (hc.isUnital_structureMap ψ hψ)).obj Q where
  toHomologicalComplex :=
    { f n := c.hom.app (Q.complex.X n)
      comm' i j _ := (c.hom.naturality (Q.complex.d i j)).symm }
  map_mul n i U x y := hc.module_map_mul ψ hψ Q n i U x y

/-- The components of the inverse of `c` as a homomorphism of right differential graded
`A`-modules. -/
noncomputable def TensoratorCompatible.moduleInv (Q : DifferentialGradedModule.{w, w, w} B) :
    (restrictCoeffFunctor α ⋙
        toposPushforward G₂ (hc.structureMap ψ) (hc.isUnital_structureMap ψ hψ)).obj Q ⟶
      (toposPushforward G₁ ψ hψ).obj Q where
  toHomologicalComplex :=
    { f n := c.inv.app (Q.complex.X n)
      comm' i j _ := (c.inv.naturality (Q.complex.d i j)).symm }
  map_mul n i U x y := by
    have e := hc.module_map_mul ψ hψ Q n i U ((c.inv.app (Q.complex.X n)).val.app U x) y
    refine (congrArg (fun z => (c.inv.app (Q.complex.X (n + i))).val.app U
      ((((toposPushforward G₂ (hc.structureMap ψ) (hc.isUnital_structureMap ψ hψ)).obj
          ((restrictCoeffFunctor α).obj Q)).mul n i).app U z y))
      (inv_hom_val_app (c := c) (Q.complex.X n) U x).symm).trans ?_
    refine (congrArg (fun z => (c.inv.app (Q.complex.X (n + i))).val.app U z) e.symm).trans ?_
    exact hom_inv_val_app (c := c) (Q.complex.X (n + i)) U _

/-- **`G₁` and `G₂` through `c` give the same direct image of differential graded modules**: the
direct image along `(G₁, ψ)` is restriction of scalars along `α` followed by the direct image along
`(G₂, ψ')`. -/
noncomputable def TensoratorCompatible.pushforwardIso :
    toposPushforward G₁ ψ hψ ≅
      restrictCoeffFunctor α ⋙
        toposPushforward G₂ (hc.structureMap ψ) (hc.isUnital_structureMap ψ hψ) :=
  NatIso.ofComponents
    (fun Q =>
      { hom := hc.moduleHom ψ hψ Q
        inv := hc.moduleInv ψ hψ Q
        hom_inv_id := Hom.ext fun n => c.hom_inv_id_app (Q.complex.X n)
        inv_hom_id := Hom.ext fun n => c.inv_hom_id_app (Q.complex.X n) })
    fun k => Hom.ext fun n => c.hom.naturality (k.toHomologicalComplex.f n)

end Comparison

section ToposComparison


variable {Y : AlgebraicGeometry.RingedTopos.{v₂, u₂, w}}
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (CategoryTheory.forget RingCat.{w})]
  [Y.J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify Y.J AddCommGrpCat.{w}]
  {X : AlgebraicGeometry.RingedTopos.{v₁, u₁, w}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (CategoryTheory.forget RingCat.{w})]
  [X.J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify X.J AddCommGrpCat.{w}]

attribute [local instance] Stacks.TensorSheafWorld.monoidalCategory

variable (f : RingedToposHom X Y)

/-! ### The comparison on sheaves of modules -/

/-- **`f_*M` is `g_*M♭`**: the identity of sheaves of `O`-modules from the direct image along
`f` to the direct image along `g` of the restriction of scalars along `α`. -/
noncomputable def directImageRestrictCoeffHom (M : SheafOfModules.{w} (toRingCat X.J X.O)) :
    (toposDirectImageModules f).obj M ⟶
      (toposDirectImageModules (inverseImageRingedToposHom f)).obj
        ((restrictCoeffSheaf (coeffMap f)).obj M) :=
  𝟙 _

/-- The inverse of `directImageRestrictCoeffHom`, again the identity. -/
noncomputable def directImageRestrictCoeffInv (M : SheafOfModules.{w} (toRingCat X.J X.O)) :
    (toposDirectImageModules (inverseImageRingedToposHom f)).obj
        ((restrictCoeffSheaf (coeffMap f)).obj M) ⟶
      (toposDirectImageModules f).obj M :=
  𝟙 _

omit [Y.J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify Y.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify X.J AddCommGrpCat.{w}] in
/-- `directImageRestrictCoeffHom` is the identity on local sections. -/
@[simp]
theorem directImageRestrictCoeffHom_val_app (M : SheafOfModules.{w} (toRingCat X.J X.O))
    (U : Y.Cᵒᵖ) (x : ((toposDirectImageModules f).obj M).val.obj U) :
    (directImageRestrictCoeffHom f M).val.app U x = x :=
  rfl

omit [Y.J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify Y.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify X.J AddCommGrpCat.{w}] in
/-- `directImageRestrictCoeffInv` is the identity on local sections. -/
@[simp]
theorem directImageRestrictCoeffInv_val_app (M : SheafOfModules.{w} (toRingCat X.J X.O))
    (U : Y.Cᵒᵖ) (x : ((toposDirectImageModules f).obj M).val.obj U) :
    (directImageRestrictCoeffInv f M).val.app U x = x :=
  rfl

/-- Morphisms of sheaves of modules which agree on local sections are equal. -/
private theorem hom_ext_of_val_app_eq {T : Type u₁} [Category.{v₁} T] {L : GrothendieckTopology T}
    {S : Sheaf L RingCat.{w}} {M N : SheafOfModules.{w} S} {φ ψ : M ⟶ N}
    (h : ∀ U x, φ.val.app U x = ψ.val.app U x) : φ = ψ :=
  SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U =>
    ModuleCat.hom_ext (LinearMap.ext (h U)))

omit [Y.J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify Y.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify X.J AddCommGrpCat.{w}] in
/-- `directImageRestrictCoeffInv` is inverse to `directImageRestrictCoeffHom`. -/
theorem directImageRestrictCoeffHom_inv (M : SheafOfModules.{w} (toRingCat X.J X.O)) :
    directImageRestrictCoeffHom f M ≫ directImageRestrictCoeffInv f M = 𝟙 _ :=
  hom_ext_of_val_app_eq fun _ _ => rfl

omit [Y.J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify Y.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify X.J AddCommGrpCat.{w}] in
/-- `directImageRestrictCoeffHom` is inverse to `directImageRestrictCoeffInv`. -/
theorem directImageRestrictCoeffInv_hom (M : SheafOfModules.{w} (toRingCat X.J X.O)) :
    directImageRestrictCoeffInv f M ≫ directImageRestrictCoeffHom f M = 𝟙 _ :=
  hom_ext_of_val_app_eq fun _ _ => rfl

omit [Y.J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify Y.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify X.J AddCommGrpCat.{w}] in
/-- The comparison is natural. -/
theorem directImageRestrictCoeffHom_naturality {M N : SheafOfModules.{w} (toRingCat X.J X.O)}
    (k : M ⟶ N) :
    (toposDirectImageModules f).map k ≫ directImageRestrictCoeffHom f N =
      directImageRestrictCoeffHom f M ≫ (toposDirectImageModules (inverseImageRingedToposHom f)).map
        ((restrictCoeffSheaf (coeffMap f)).map k) :=
  hom_ext_of_val_app_eq fun _ _ => rfl

omit [Y.J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify Y.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify X.J AddCommGrpCat.{w}] in
/-- The inverse comparison is natural. -/
theorem directImageRestrictCoeffInv_naturality {M N : SheafOfModules.{w} (toRingCat X.J X.O)}
    (k : M ⟶ N) :
    (toposDirectImageModules (inverseImageRingedToposHom f)).map
        ((restrictCoeffSheaf (coeffMap f)).map k) ≫ directImageRestrictCoeffInv f N =
      directImageRestrictCoeffInv f M ≫ (toposDirectImageModules f).map k :=
  hom_ext_of_val_app_eq fun _ _ => rfl

/-- The direct image along `g` is additive, with its source spelled as sheaves of modules over
`f⁻¹O` on the site of `X`. -/
instance additive_toposDirectImageModules_inverseImageRingedToposHom :
    @Functor.Additive (SheafOfModules.{w} (toRingCat X.J (inverseImageStructureSheaf f)))
      (SheafOfModules.{w} (toRingCat Y.J Y.O)) SheafOfModules.instCategory
      SheafOfModules.instCategory
      (SheafOfModules.instPreadditive (toRingCat X.J (inverseImageStructureSheaf f)))
      (SheafOfModules.instPreadditive (toRingCat Y.J Y.O))
      (toposDirectImageModules (inverseImageRingedToposHom f)) :=
  toposDirectImageModules_additive (inverseImageRingedToposHom f)

/-- **`f_* ≅ restrictCoeffSheaf α ⋙ g_*`**, the identity on underlying sheaves. -/
noncomputable def directImageRestrictCoeffIso :
    toposDirectImageModules f ≅
      restrictCoeffSheaf (coeffMap f) ⋙ toposDirectImageModules (inverseImageRingedToposHom f) :=
  NatIso.ofComponents
    (fun M =>
      { hom := directImageRestrictCoeffHom f M
        inv := directImageRestrictCoeffInv f M
        hom_inv_id := directImageRestrictCoeffHom_inv f M
        inv_hom_id := directImageRestrictCoeffInv_hom f M })
    fun k => directImageRestrictCoeffHom_naturality f k

omit [Y.J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify Y.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify X.J AddCommGrpCat.{w}] in
/-- `f_* ≅ restrictCoeffSheaf α ⋙ g_*` is the identity on local sections. -/
@[simp]
theorem directImageRestrictCoeffIso_hom_val_app (M : SheafOfModules.{w} (toRingCat X.J X.O))
    (U : Y.Cᵒᵖ) (x : ((toposDirectImageModules f).obj M).val.obj U) :
    ((directImageRestrictCoeffIso f).hom.app M).val.app U x = x :=
  rfl

omit [Y.J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify Y.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify X.J AddCommGrpCat.{w}] in
/-- The inverse of `f_* ≅ restrictCoeffSheaf α ⋙ g_*` is the identity on local sections. -/
@[simp]
theorem directImageRestrictCoeffIso_inv_val_app (M : SheafOfModules.{w} (toRingCat X.J X.O))
    (U : Y.Cᵒᵖ) (x : ((toposDirectImageModules f).obj M).val.obj U) :
    ((directImageRestrictCoeffIso f).inv.app M).val.app U x = x :=
  rfl

/-- **The tensorators of `f_*` and `g_*` agree on pure tensors**, by
`toposDirectImageModules_μ_comp_map_app`. -/
theorem directImageRestrictCoeffTensorator :
    @TensoratorCompatible _ _ _ _ _ _ _ _ (coeffMap f) _ _ _ _ _ _ _ (toposDirectImageModules f)
      (toposDirectImageModules_laxMonoidal f)
      (toposDirectImageModules (inverseImageRingedToposHom f))
      (toposDirectImageModules_laxMonoidal (inverseImageRingedToposHom f))
      (directImageRestrictCoeffIso f) := by
  intro M N P m m' hm V x y
  have h' := (toposDirectImageModules_μ_comp_map_app f m m' hm V x y).trans
    (directImageRestrictCoeffIso_inv_val_app f P V _).symm
  rw [directImageRestrictCoeffIso_hom_val_app, directImageRestrictCoeffIso_hom_val_app]
  exact h'

variable {A : DifferentialGradedAlgebra.{w, w} (toRingCat Y.J Y.O)}
  {B : DifferentialGradedAlgebra.{w, w} (toRingCat X.J X.O)}
  (ψ : A ⟶ toposPushforwardAlgebra (toposDirectImageModules f) B) (hψ : ψ.IsUnital)

/-- **`f_*B` is `g_*B♭`**: the identity of sheaves of differential graded `O`-algebras from the
direct image of `B` along `f` to the direct image along `g` of its restriction of scalars along
`α`. -/
noncomputable abbrev directImageRestrictCoeffAlgebraHom (B : DifferentialGradedAlgebra.{w, w}
    (toRingCat X.J X.O)) :
    toposPushforwardAlgebra (toposDirectImageModules f) B ⟶
      toposPushforwardAlgebra (toposDirectImageModules (inverseImageRingedToposHom f))
        (B.restrictCoeff (coeffMap f)) :=
  @TensoratorCompatible.algebraHom _ _ _ _ _ _ _ _ (coeffMap f) _ _ _ _ _ _ _
    (toposDirectImageModules f) (toposDirectImageModules_laxMonoidal f) _
    (toposDirectImageModules (inverseImageRingedToposHom f))
    (toposDirectImageModules_laxMonoidal (inverseImageRingedToposHom f)) _
    (directImageRestrictCoeffIso f) (directImageRestrictCoeffTensorator f) B

/-- **`ψ' : A ⟶ g_*B♭`**, the structure homomorphism `ψ : A ⟶ f_*B` read into the direct image
along `g` of the restriction of scalars of `B` along `α`. -/
noncomputable abbrev restrictCoeffStructureMap :
    A ⟶ toposPushforwardAlgebra (toposDirectImageModules (inverseImageRingedToposHom f))
      (B.restrictCoeff (coeffMap f)) :=
  @TensoratorCompatible.structureMap _ _ _ _ _ _ _ _ (coeffMap f) _ _ _ _ _ _ _
    (toposDirectImageModules f) (toposDirectImageModules_laxMonoidal f) _
    (toposDirectImageModules (inverseImageRingedToposHom f))
    (toposDirectImageModules_laxMonoidal (inverseImageRingedToposHom f)) _
    (directImageRestrictCoeffIso f) (directImageRestrictCoeffTensorator f) _ _ ψ

include hψ in
/-- `ψ' : A ⟶ g_*B♭` is unital. -/
theorem isUnital_restrictCoeffStructureMap : (restrictCoeffStructureMap f ψ).IsUnital :=
  @TensoratorCompatible.isUnital_structureMap _ _ _ _ _ _ _ _ (coeffMap f) _ _ _ _ _ _ _
    (toposDirectImageModules f) (toposDirectImageModules_laxMonoidal f) _
    (toposDirectImageModules (inverseImageRingedToposHom f))
    (toposDirectImageModules_laxMonoidal (inverseImageRingedToposHom f)) _
    (directImageRestrictCoeffIso f) (directImageRestrictCoeffTensorator f) _ _ ψ hψ

/-- **`f_{*,ψ} ≅ restrictCoeffFunctor α ⋙ g_{*,ψ'}`**: the direct image of right differential
graded `B`-modules along `(f, ψ)` is restriction of scalars to `B♭` followed by the direct image
along `(g, ψ')`. -/
noncomputable def toposPushforwardRestrictCoeffIso :
    toposPushforward (toposDirectImageModules f) ψ hψ ≅
      restrictCoeffFunctor (coeffMap f) ⋙
        toposPushforward (toposDirectImageModules (inverseImageRingedToposHom f))
          (restrictCoeffStructureMap f ψ) (isUnital_restrictCoeffStructureMap f ψ hψ) :=
  @TensoratorCompatible.pushforwardIso _ _ _ _ _ _ _ _ (coeffMap f) _ _ _ _ _ _ _
    (toposDirectImageModules f) (toposDirectImageModules_laxMonoidal f) _
    (toposDirectImageModules (inverseImageRingedToposHom f))
    (toposDirectImageModules_laxMonoidal (inverseImageRingedToposHom f)) _
    (directImageRestrictCoeffIso f) (directImageRestrictCoeffTensorator f) _ _ ψ hψ

end ToposComparison

end SheafOfModules.DifferentialGradedModule

end
