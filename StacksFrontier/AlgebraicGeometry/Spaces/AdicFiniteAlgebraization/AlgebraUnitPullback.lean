module

public import StacksFrontier.AlgebraicGeometry.Spaces.AdicFiniteAlgebraization.AffineTowerSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.AlgebraPullbackChartSectionTranspose
public import StacksFrontier.AlgebraicGeometry.Spaces.AlgebraPullbackChartSections
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheafPullbackUnitIsoComp
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.ComparisonAlgebraicSpacesTransport

/-!
# The structure map of an algebra sheaf commutes with pullback

Let `A` be a sheaf of commutative `𝒪_F`-algebras on the small étale site of an algebraic space
`F`.  Its structure-algebra maps `𝒪_F(U) ⟶ A(U)` are `𝒪_F(U)`-linear for the module structure on
`A(U)` they induce, so they form a morphism of `𝒪_F`-modules `𝒪_F ⟶ A`, the *structure map* of
`A`, natural in `A`.

For a morphism `g : Y ⟶ X` of algebraic spaces and an `𝒪_X`-algebra `A`, the pullback of the
structure map of `A` is the structure map of the pullback algebra `g^*A`, once `g^*𝒪_X` is
identified with `𝒪_Y` and `g^*(A)` as a module with the module underlying `g^*A`.  Both sides are
morphisms out of an inverse image of modules, so they are compared on the chart sections of the
chart diagrams over `g`, where the identification of `g^*A` takes the chart section of a section
`a` to the algebra chart section of `a`, and the latter is a homomorphism of algebras over the
pullback of regular functions.

Applied to the direct images `𝒜_n = (W n ⟶ Z n)_* 𝒪_{W n}` along a cartesian affine tower, this
says that the transition isomorphisms `t n ^* 𝒜_{n + 1} ≅ 𝒜_n` are compatible with the structure
maps `𝒪_{Z n} ⟶ 𝒜_n`.

## Main definitions

* `AlgebraicGeometry.Space.AlgebraSheaf.unitToUnderlyingModule`: the structure map `𝒪_F ⟶ A` of
  an algebra sheaf, as a morphism of `𝒪_F`-modules.

## Main results

* `AlgebraicGeometry.Space.AlgebraSheaf.unitToUnderlyingModule_comp_underlyingModuleMap`: the
  structure maps are natural in the algebra sheaf.
* `AlgebraicGeometry.Space.underlyingModuleAlgebraPullbackModulePullbackIso_hom_chartSection`:
  the identification of `g^*(A)` with the module underlying `g^*A` on chart sections.
* `AlgebraicGeometry.Space.modulePullback_map_unitToUnderlyingModule_comp`: **the pullback of
  the structure map of `A` is the structure map of `g^*A`.**
* `AlgebraicGeometry.Space.`
  `modulePullback_map_unitToUnderlyingModule_comp_affineTowerModuleTransition`: the same for
  the transition isomorphisms of a cartesian affine tower.

## References

* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
* [Stacks Project, Tag 0A01](https://stacks.math.columbia.edu/tag/0A01)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}

namespace AlgebraSheaf

/-- The structure-algebra map of an algebra sheaf over an étale chart, as a linear map from the
sections of the structure sheaf to the sections of the underlying module. -/
def unitToUnderlyingModuleLinear (A : AlgebraSheaf.{u, u} B S hS F hF)
    (U : (SmallEtale B S hS F)ᵒᵖ) :
    (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS F hF).O))).val.obj U →ₗ[(Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS F hF).O).obj.obj U] (underlyingModule A).val.obj U where
  toFun r := A.algebraMap U r
  map_add' r r' := map_add (A.algebraMap U) r r'
  map_smul' r r' := map_mul (A.algebraMap U) r r'

/-- The structure map `𝒪_F ⟶ A` of an algebra sheaf, as a morphism of `𝒪_F`-modules from the
structure sheaf to the underlying module of `A`. -/
def unitToUnderlyingModule (A : AlgebraSheaf.{u, u} B S hS F hF) :
    SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS F hF).O)) ⟶ A.underlyingModule :=
  show SheafOfModules.Hom _ _ from
  { val :=
    { app U := ConcreteCategory.ofHom
        (C := ModuleCat
          ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).obj.obj U))
        (unitToUnderlyingModuleLinear A U)
      naturality i :=
        ModuleCat.hom_ext (LinearMap.ext fun r => (A.algebraMap_natural i r).symm) } }

/-- The structure map of an algebra sheaf acts on sections as the structure-algebra map. -/
@[simp]
theorem unitToUnderlyingModule_val_app_apply (A : AlgebraSheaf.{u, u} B S hS F hF)
    (U : (SmallEtale B S hS F)ᵒᵖ) (r : (structureSheaf B S hS F hF).obj.obj U) :
    (unitToUnderlyingModule A).val.app U r = A.algebraMap U r :=
  rfl

/-- The structure maps commute with a morphism of algebra sheaves. -/
@[simp]
theorem unitToUnderlyingModule_comp_underlyingModuleMap {A C : AlgebraSheaf.{u, u} B S hS F hF}
    (f : A ⟶ C) :
    unitToUnderlyingModule A ≫ underlyingModuleMap f = unitToUnderlyingModule C :=
  SheafOfModules.hom_ext <|
    PresheafOfModules.hom_ext fun U => ModuleCat.hom_ext (LinearMap.ext fun r => f.comm U r)

end AlgebraSheaf

variable (B S hS) {X Y : AlgebraicSpaces B S hS}

/-- **The identification of `g^*(A_mod)` with the module underlying `g^*A` carries the chart
section of a section `a` of `A` to the algebra chart section of `a`.** -/
theorem underlyingModuleAlgebraPullbackModulePullbackIso_hom_chartSection (g : Y ⟶ X)
    (A : AlgebraSheaf.{u, u} B S hS X.1 X.2) (d : ChartDiagram B S hS Y.1 X.1 g.hom)
    (a : A.right.obj.obj (op d.V)) :
    (underlyingModuleAlgebraPullbackModulePullbackIso B S hS g A).hom.val.app (op d.U)
        (modulePullbackChartSection B S hS g A.underlyingModule d a) =
      algebraPullbackChartSection B S hS g A d a := by
  refine (underlyingModuleAlgebraPullbackModulePullbackIso_chartSection B S hS g A d a).trans ?_
  have hu := Adjunction.homEquiv_unit (ringSheafPullbackAdjunction B S hS g) A.right
    ((algebraPullback B S hS g).obj A).right ((algebraPullbackMap B S hS g).app A)
  refine Eq.trans (congrArg (fun m : A.right ⟶
      (ringSheafPushforward B S hS g).obj ((algebraPullback B S hS g).obj A).right =>
    ringChartProjection B S hS g ((algebraPullback B S hS g).obj A).right d
      ((m.hom.app (op d.V)).hom a)) hu) ?_
  exact ringChartProjection_naturality B S hS g ((algebraPullbackMap B S hS g).app A) d _

/-- Two composites out of an inverse image of modules which agree, factor after factor, on the
chart sections are equal. -/
private theorem modulePullback_comp_eq_comp_of_chartSection (g : Y ⟶ X)
    (M : Modules.{u, u} B S hS X.1 X.2) {N N' P : Modules.{u, u} B S hS Y.1 Y.2}
    (a : (modulePullback B S hS g).obj M ⟶ N) (b : N ⟶ P)
    (a' : (modulePullback B S hS g).obj M ⟶ N') (b' : N' ⟶ P)
    (h : ∀ (e : ChartDiagram B S hS Y.1 X.1 g.hom) (s : M.val.obj (op e.V)),
      b.val.app (op e.U) (a.val.app (op e.U) (modulePullbackChartSection B S hS g M e s)) =
        b'.val.app (op e.U) (a'.val.app (op e.U) (modulePullbackChartSection B S hS g M e s))) :
    a ≫ b = a' ≫ b' :=
  modulePullback_hom_ext_of_chartSection B S hS g M P _ _ h

/-- **The pullback of the structure map of an algebra sheaf is the structure map of the pullback
algebra.**  Along `g : Y ⟶ X`, the pullback `g^*𝒪_X ⟶ g^*(A_mod)` of the structure map of `A`,
followed by the identification `g^*(A_mod) ≅ (g^*A)_mod`, is the identification
`g^*𝒪_X ≅ 𝒪_Y` followed by the structure map of `g^*A`. -/
theorem modulePullback_map_unitToUnderlyingModule_comp (g : Y ⟶ X)
    (A : AlgebraSheaf.{u, u} B S hS X.1 X.2) :
    (modulePullback B S hS g).map (AlgebraSheaf.unitToUnderlyingModule A) ≫
        (underlyingModuleAlgebraPullbackModulePullbackIso B S hS g A).hom =
      (modulePullbackUnitIso B S hS g).hom ≫
        AlgebraSheaf.unitToUnderlyingModule ((algebraPullback B S hS g).obj A) := by
  refine modulePullback_comp_eq_comp_of_chartSection B S hS g _ _ _ _ _ fun e s => ?_
  have h1 : ((modulePullback B S hS g).map (AlgebraSheaf.unitToUnderlyingModule A)).val.app
        (op e.U) (modulePullbackChartSection B S hS g _ e s) =
      modulePullbackChartSection B S hS g A.underlyingModule e (A.algebraMap (op e.V) s) :=
    modulePullbackChartSection_map B S hS g _ (AlgebraSheaf.unitToUnderlyingModule A) e s
  have h2 := underlyingModuleAlgebraPullbackModulePullbackIso_hom_chartSection B S hS g A e
    (A.algebraMap (op e.V) s)
  have h3 := algebraPullbackChartSection_algebraMap B S hS g A e s
  have h4 : (modulePullbackUnitIso B S hS g).hom.val.app (op e.U)
        (modulePullbackChartSection B S hS g _ e s) = chartDiagramRestrict B S hS g e s :=
    modulePullbackUnitIso_hom_val_app_chartSection B S hS g e s
  rw [h1, h4]
  exact h2.trans h3

/-! ### The direct images along a cartesian affine tower -/

section AffineTower

variable {Z : ℕ → AlgebraicSpaces B S hS} (t : ∀ n, Z n ⟶ Z (n + 1))
  (W : ∀ n, AffineOver B S hS (Z n)) (s : ∀ n, (W n).obj.left ⟶ (W (n + 1)).obj.left)
  (hcart : ∀ n, IsPullback (s n) (W n).obj.hom (W (n + 1)).obj.hom (t n))

/-- **The transition isomorphisms of the direct images along a cartesian affine tower are
compatible with the structure maps**: the pullback along `t n` of the structure map
`𝒪_{Z (n + 1)} ⟶ 𝒜_{n + 1}`, followed by the transition `t n ^* 𝒜_{n + 1} ≅ 𝒜_n`, is the
identification `t n ^* 𝒪_{Z (n + 1)} ≅ 𝒪_{Z n}` followed by the structure map of `𝒜_n`. -/
theorem modulePullback_map_unitToUnderlyingModule_comp_affineTowerModuleTransition (n : ℕ) :
    (modulePullback B S hS (t n)).map
        (AlgebraSheaf.unitToUnderlyingModule (pushforwardAlgebra B S hS (W (n + 1)).obj)) ≫
        (affineTowerModuleTransition B S hS t W s hcart n).hom =
      (modulePullbackUnitIso B S hS (t n)).hom ≫
        AlgebraSheaf.unitToUnderlyingModule (pushforwardAlgebra B S hS (W n).obj) := by
  have h := modulePullback_map_unitToUnderlyingModule_comp B S hS (t n)
    (pushforwardAlgebra B S hS (W (n + 1)).obj)
  have h' := AlgebraSheaf.unitToUnderlyingModule_comp_underlyingModuleMap
    (affineTowerAlgebraTransition B S hS t W s hcart n).hom
  calc _ = ((modulePullback B S hS (t n)).map
        (AlgebraSheaf.unitToUnderlyingModule (pushforwardAlgebra B S hS (W (n + 1)).obj)) ≫
        (underlyingModuleAlgebraPullbackModulePullbackIso B S hS (t n) _).hom) ≫
        AlgebraSheaf.underlyingModuleMap (affineTowerAlgebraTransition B S hS t W s hcart n).hom :=
        (Category.assoc _ _ _).symm
    _ = _ := by rw [h, Category.assoc, h']

end AffineTower

end AlgebraicGeometry.Space

end
