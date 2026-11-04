module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedSectionRealization
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedSectionCochain

/-!
# Homogeneous maps of presheaves of section modules and their realizations

Let `A` be a sheaf of differential graded algebras on a category with the chaotic topology. A
natural family of homogeneous maps of degree `k` between two presheaves of section modules `X`
and `Y` — homogeneous maps `X(U) ⟶ Y(U)` of differential graded `A(U)`-modules commuting with
the restriction homomorphisms — realizes to a cochain of degree `k` between the realizations,
which commutes with the action of `A`: in degree `p` over `U` it is the restriction of the map
over `U` to the homogeneous elements of degree `p`. Realization is additive, commutes with the
differentials of the hom complexes, with composition, and with morphisms.

This is the cochain-level form of the realization functor
`SheafOfModules.DifferentialGradedModule.SectionSystem.realizeFunctor`.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.SectionSystem.HomogeneousFamily`: a natural family of
  homogeneous maps of degree `k` between presheaves of section modules.
* `SheafOfModules.DifferentialGradedModule.SectionSystem.HomogeneousFamily.realizeCochain`: its
  realization, a cochain of degree `k` between the realizations.

## Main results

* `….HomogeneousFamily.realizeCochain_add`, `realizeCochain_d`, `realizeCochain_comp` and
  `realizeCochain_ofHom`: realization of homogeneous families is additive, compatible with the
  differentials and with composition, and on a morphism it is the realization of the morphism.
* `….HomogeneousFamily.isActionLinear_realizeCochain`: the realization commutes with the action.

## References

* [Stacks Project, Section 24.33 (Tag 0GZ8)](https://stacks.math.columbia.edu/tag/0GZ8)
* [Stacks Project, Tag 09LC](https://stacks.math.columbia.edu/tag/09LC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Sheaf CochainComplex.HomComplex

universe t m v u

namespace SheafOfModules.DifferentialGradedModule.SectionSystem

attribute [local instance] GradedAlgebra.sectionsGOne GradedAlgebra.sectionsGMul
  GradedAlgebra.sectionsGRing Stacks.uliftIntAlgebra pieceModule

/-- A linear map applied to `(φ - c • ψ) x`. -/
theorem linearMap_sub_smul_apply {R M N P : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N]
    [AddCommGroup P] {_ : Module R M} {_ : Module R N} {_ : Module R P} (g : N →ₗ[R] P)
    (φ ψ : M →ₗ[R] N)
    (c : R) (x : M) : g ((φ - c • ψ) x) = g (φ x) - c • g (ψ x) := by
  simp

/-- The value of `φ - c • ψ` for linear maps, for any module structures. -/
theorem linearMap_sub_smul_apply' {R M N : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N]
    {_ : Module R M} {_ : Module R N} (φ ψ : M →ₗ[R] N) (c : R) (x : M) :
    (φ - c • ψ) x = φ x - c • ψ x :=
  rfl

variable {C : Type u} [Category.{v} C]
  [(⊥ : GrothendieckTopology C).HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})]
  {Osharp : Sheaf (⊥ : GrothendieckTopology C) CommRingCat.{t}}
  {A : DifferentialGradedAlgebra.{t, m} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp)}

variable (X Y Z : SectionSystem A)

/-- **A natural family of homogeneous maps of degree `k`** between presheaves of section modules:
a homogeneous map `X(U) ⟶ Y(U)` of degree `k` of differential graded `A(U)`-modules for every
object `U`, commuting with the restriction homomorphisms. -/
@[ext]
structure HomogeneousFamily (k : ℤ) where
  /-- The homogeneous map over `U`. -/
  app (U : Cᵒᵖ) :
    _root_.DifferentialGradedModule.HomogeneousMap (A.sectionAlgebra U) (X.obj U) (Y.obj U) k
  /-- The homogeneous maps commute with restriction. -/
  naturality {U V : Cᵒᵖ} (a : V ⟶ U) (x : (X.obj V).M) :
    Y.restrFun a ((app V).1 x) = (app U).1 (X.restrFun a x)

namespace HomogeneousFamily

variable {X Y Z}

/-- The sum of two natural families of homogeneous maps. -/
instance {k : ℤ} : Add (HomogeneousFamily X Y k) where
  add f g :=
    { app := fun U ↦ f.app U + g.app U
      naturality := fun a x ↦ by
        show Y.restrFun a ((f.app _).1 x + (g.app _).1 x) = (f.app _).1 _ + (g.app _).1 _
        rw [Y.restrFun_add, f.naturality, g.naturality] }

/-- The component of a sum of natural families over `U` is the sum of the components. -/
@[simp] theorem add_app {k : ℤ} (f g : HomogeneousFamily X Y k) (U : Cᵒᵖ) :
    (f + g).app U = f.app U + g.app U :=
  rfl

/-- The differential of a natural family of homogeneous maps: over `U` it is the differential of
the hom complex `Hom(X(U), Y(U))`. -/
def d {k : ℤ} (f : HomogeneousFamily X Y k) : HomogeneousFamily X Y (k + 1) where
  app U := _root_.DifferentialGradedModule.homogeneousMapDifferential (A.sectionAlgebra U) (f.app U)
  naturality a x := by
    rw [_root_.DifferentialGradedModule.homogeneousMapDifferential_val,
      _root_.DifferentialGradedModule.homogeneousMapDifferential_val, Y.restrFun_apply,
      linearMap_sub_smul_apply, LinearMap.comp_apply, LinearMap.comp_apply, ← Y.restrFun_apply,
      ← Y.restrFun_apply, Y.restrFun_d, f.naturality, f.naturality, X.restrFun_d]
    rfl

/-- The component of the differential `f.d` over `U` is the differential of `f.app U` in the hom
complex `Hom(X(U), Y(U))`. -/
@[simp] theorem d_app {k : ℤ} (f : HomogeneousFamily X Y k) (U : Cᵒᵖ) :
    f.d.app U =
      _root_.DifferentialGradedModule.homogeneousMapDifferential (A.sectionAlgebra U) (f.app U) :=
  rfl

/-- The composite of two natural families of homogeneous maps. -/
def comp {k l m : ℤ} (h : l + k = m) (g : HomogeneousFamily Y Z l) (f : HomogeneousFamily X Y k) :
    HomogeneousFamily X Z m where
  app U := _root_.DifferentialGradedModule.homogeneousMapComp (A.sectionAlgebra U) h
    (g.app U) (f.app U)
  naturality a x := by
    show Z.restrFun a ((g.app _).1 ((f.app _).1 x)) = (g.app _).1 ((f.app _).1 (X.restrFun a x))
    rw [g.naturality, f.naturality]

omit [(⊥ : GrothendieckTopology C).HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] in
/-- The component of `comp h g f` over `U` is the composite of the components of `g` and `f`. -/
@[simp] theorem comp_app {k l m : ℤ} (h : l + k = m) (g : HomogeneousFamily Y Z l)
    (f : HomogeneousFamily X Y k) (U : Cᵒᵖ) :
    (comp h g f).app U =
      _root_.DifferentialGradedModule.homogeneousMapComp (A.sectionAlgebra U) h (g.app U)
        (f.app U) :=
  rfl

/-- The natural family of homogeneous maps of degree zero of a morphism of presheaves of section
modules. -/
def ofHom (φ : X ⟶ Y) : HomogeneousFamily X Y 0 where
  app U := (_root_.DifferentialGradedModule.cocycleOfHom (A.sectionAlgebra U) (φ.app U)).1
  naturality a x := φ.naturality a x

omit [(⊥ : GrothendieckTopology C).HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] in
/-- The component of `ofHom φ` over `U` is the homogeneous map of degree zero of `φ.app U`. -/
@[simp] theorem ofHom_app (φ : X ⟶ Y) (U : Cᵒᵖ) :
    (ofHom φ).app U =
      (_root_.DifferentialGradedModule.cocycleOfHom (A.sectionAlgebra U) (φ.app U)).1 :=
  rfl

/-! ### Realization -/

/-- A natural family of homogeneous maps of degree `k` on the homogeneous elements of degree `p`
over `U`, landing in degree `q = p + k`. -/
def appPiece {k : ℤ} (f : HomogeneousFamily X Y k) (U : Cᵒᵖ) (p q : ℤ) (h : p + k = q) :
    (X.obj U).grading p →+ (Y.obj U).grading q where
  toFun x := ⟨(f.app U).1 x, h ▸ (f.app U).2.1 p x x.2⟩
  map_zero' := Subtype.ext (map_zero (f.app U).1)
  map_add' x y := Subtype.ext (map_add (f.app U).1 (x : (X.obj U).M) y)

/-- A natural family of homogeneous maps of degree `k`, as a morphism from the degree-`p` piece
of the realization of `X` to the degree-`q` piece of the realization of `Y`, `q = p + k`. -/
def pieceMap {k : ℤ} (f : HomogeneousFamily X Y k) (p q : ℤ) (h : p + k = q) :
    X.pieceSheaf p ⟶ Y.pieceSheaf q :=
  ⟨PresheafOfModules.homMk
    { app := fun U ↦ AddCommGrpCat.ofHom (f.appPiece U p q h)
      naturality := fun V U a ↦ by
        ext x
        exact Subtype.ext (f.naturality a ((show (X.obj V).grading p from x) : (X.obj V).M)).symm }
    (fun U r x ↦ Subtype.ext ((f.app U).2.2 (A.sectionScalarAlg U r) _))⟩

/-- **The realization of a natural family of homogeneous maps of degree `k`**, a cochain of
degree `k` between the realizations. -/
def realizeCochain {k : ℤ} (f : HomogeneousFamily X Y k) :
    Cochain X.realize.complex Y.realize.complex k :=
  Cochain.mk fun p q h ↦ f.pieceMap p q h

/-- On a homogeneous element `x` of degree `p` over `U`, the component of `realizeCochain f` from
degree `p` to degree `q` is `f.app U` applied to `x`. -/
theorem coe_realizeCochain_v {k : ℤ} (f : HomogeneousFamily X Y k) (p q : ℤ) (h : p + k = q)
    (U : Cᵒᵖ) (x : (X.complex.X p).val.obj U) :
    ((Y.cElt (((realizeCochain f).v p q h).val.app U x) : (Y.obj U).grading q) : (Y.obj U).M) =
      (f.app U).1 (X.cElt x : (X.obj U).grading p) := by
  simp only [realizeCochain]
  rfl

/-- Two cochains between realizations agreeing on all homogeneous elements are equal. -/
theorem realize_cochain_ext {k : ℤ} {c c' : Cochain X.realize.complex Y.realize.complex k}
    (h : ∀ (p q : ℤ) (hpq : p + k = q) (U : Cᵒᵖ) (x : (X.complex.X p).val.obj U),
      ((Y.cElt ((c.v p q hpq).val.app U x) : (Y.obj U).grading q) : (Y.obj U).M) =
        (Y.cElt ((c'.v p q hpq).val.app U x) : (Y.obj U).grading q)) : c = c' :=
  Cochain.ext _ _ fun p q hpq ↦ by
    apply SheafOfModules.hom_ext
    ext U x
    exact Y.cElt_injective (h p q hpq U x)

/-- Evaluating a sum of morphisms of sheaves of modules at a local section. -/
private theorem add_val_app_apply {p q : ℤ} {U : Cᵒᵖ} (x : (X.complex.X p).val.obj U)
    (a b : X.complex.X p ⟶ Y.complex.X q) : (a + b).val.app U x = a.val.app U x + b.val.app U x :=
  map_add (evalSectionHom U x) a b

/-- **Realization is additive.** -/
theorem realizeCochain_add {k : ℤ} (f g : HomogeneousFamily X Y k) :
    realizeCochain (f + g) = realizeCochain f + realizeCochain g :=
  realize_cochain_ext fun p q hpq U x ↦ by
    rw [coe_realizeCochain_v, Cochain.add_v,
      add_val_app_apply x,
      Y.coe_cElt_add, coe_realizeCochain_v, coe_realizeCochain_v]
    rfl

/-- **Realization commutes with the differentials of the hom complexes.** -/
theorem realizeCochain_d {k : ℤ} (f : HomogeneousFamily X Y k) :
    realizeCochain f.d = δ k (k + 1) (realizeCochain f) :=
  realize_cochain_ext fun p q hpq U x ↦ by
    rw [coe_realizeCochain_v, δ_v k (k + 1) rfl _ p q hpq (p + k) (p + 1) (by omega) rfl,
      add_val_app_apply x,
      show ∀ (c : ℤˣ) (a : X.complex.X p ⟶ Y.complex.X q), (c • a).val.app U x =
        (c : ℤ) • a.val.app U x from fun c a ↦ by
          rw [Units.smul_def]
          exact map_zsmul (evalSectionHom U x) (c : ℤ) a,
      Y.coe_cElt_add, Y.coe_cElt_zsmul, comp_val_app_apply, comp_val_app_apply,
      Y.coe_cElt_d' (by omega), coe_realizeCochain_v, coe_realizeCochain_v,
      X.coe_cElt_d' rfl, d_app, _root_.DifferentialGradedModule.homogeneousMapDifferential_val,
      linearMap_sub_smul_apply', LinearMap.comp_apply, LinearMap.comp_apply]
    exact (sub_eq_add_neg _ _).trans (congrArg (_ + ·)
      ((congrArg Neg.neg (uliftInt_smul_eq' (Y.obj U).module _ _)).trans
        (by rw [down_gradedSign, Int.negOnePow_succ, Units.val_neg, neg_smul])))

/-- **Realization preserves composition.** -/
theorem realizeCochain_comp {k l m : ℤ} (h : k + l = m) (f : HomogeneousFamily X Y k)
    (g : HomogeneousFamily Y Z l) :
    realizeCochain (comp (show l + k = m by omega) g f) =
      (realizeCochain f).comp (realizeCochain g) h :=
  realize_cochain_ext fun p q hpq U x ↦ by
    rw [coe_realizeCochain_v, Cochain.comp_v _ _ h p (p + k) q rfl (by omega), comp_val_app_apply,
      coe_realizeCochain_v, coe_realizeCochain_v, comp_app,
      _root_.DifferentialGradedModule.homogeneousMapComp_val, LinearMap.comp_apply]

/-- **On a morphism, realization is the realization of the morphism.** -/
theorem realizeCochain_ofHom (φ : X ⟶ Y) :
    realizeCochain (ofHom φ) = Cochain.ofHom (realizeMap φ).toHomologicalComplex :=
  realize_cochain_ext fun p q hpq U x ↦ by
    obtain rfl : p = q := by omega
    rw [coe_realizeCochain_v, Cochain.ofHom_v, coe_realizeMap_f]
    rfl

end HomogeneousFamily

section ActionLinear

variable {C : Type u} [Category.{u} C]
  [(⊥ : GrothendieckTopology C).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  {Osharp : Sheaf (⊥ : GrothendieckTopology C) CommRingCat.{u}}
  {A : DifferentialGradedAlgebra.{u, m} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp)}
  {X Y : SectionSystem A}

/-- **The realization of a natural family of homogeneous maps commutes with the action.** -/
theorem HomogeneousFamily.isActionLinear_realizeCochain {k : ℤ} (f : HomogeneousFamily X Y k) :
    IsActionLinear (X := ⟨C, ⊥, Osharp⟩) A f.realizeCochain :=
  fun p _ i _ U x a ↦
    Y.cElt_heq rfl ((f.app U).2.2 (A.sectionOf U i a) (X.cElt x : (X.obj U).grading p))

end ActionLinear

end SheafOfModules.DifferentialGradedModule.SectionSystem
