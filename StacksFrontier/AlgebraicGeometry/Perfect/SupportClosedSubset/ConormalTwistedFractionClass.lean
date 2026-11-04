module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyFiniteFreeSummand.LeftDualOnSpace
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.SupportedFractionNaturality
public import StacksFrontier.AlgebraicGeometry.Blowup.ExceptionalTwist
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The twisted fraction class of a family of global equations

Let `X` be a scheme, let `Z ⊆ X` be a closed subset, let `f₁, …, f_c ∈ Γ(X, 𝒪_X)` be functions
with zero locus `Z`, and let `ℱ` be a quasi-coherent `𝒪_X`-module.  Given a module `line` with a
global section `wedge f` for every such family, multiplied by `det(a)` when the family is changed
by a matrix `a` (the datum `ConormalWedge`), the *twisted fraction class* sends `λ ⊗ s` to the
class `c_f(λ(wedge f) s)` of Stacks 0G7Q.  By Stacks 0G7S and the determinant law the twisted
class does not depend on the family, and it is functorial in `ℱ`:

`c_g(λ(wedge g) s) = c_g(det(a) λ(wedge f) s) = c_f(λ(wedge f) s)`.

For a closed immersion `i : Z ⟶ X` of finite presentation whose conormal sheaf is finite locally
free of rank `c`, with `line = i_*⋀^c 𝒞_{Z/X}` and `wedge f = [f₁] ∧ ⋯ ∧ [f_c]`, the glued map
is `Stacks.Perfect.ConormalClass.conormalTwistClass`.

## Main definitions

* `Stacks.Perfect.SupportedFraction.ConormalWedge`: a module `line` on `X` with a global section
  `wedge f` for each family of `c` equations cutting out `Z`, and the determinant transformation
  law.
* `Stacks.Perfect.SupportedFraction.evalWedge`: evaluation of the dual line at a global
  trivialization, `line^∨ ⟶ 𝒪_X`, through the dual `Stacks.SheafOfModules.OnSpace.dualSheaf`
  and the evaluation pairing of Stacks 0FNV.
* `Stacks.Perfect.SupportedFraction.twistedFractionClass`: the twisted fraction class, with
  source `line^∨ ⊗ i_*i^*ℱ`.
* `Stacks.Perfect.SupportedFraction.twistedFractionSource`: the same map read on
  `line^∨ ⊗ ℱ` through the canonical epimorphism `ℱ ↠ i_*i^*ℱ`.
* `Stacks.Perfect.SupportedFraction.zeroConormalWedge` and
  `Stacks.Perfect.SupportedFraction.unitConormalWedge`: the zero datum and a datum whose wedge is
  not zero.

## Main results

* `Stacks.Perfect.SupportedFraction.twistedFractionSource_eq`: two families of `c` equations
  cutting out the same closed subset and related by a matrix give the same twisted map.
* `Stacks.Perfect.SupportedFraction.twistedFractionSource_natural`: the twisted map is
  functorial in the quasi-coherent module `ℱ`.
* `Stacks.Perfect.SupportedFraction.whiskerRight_globalSmul_unit_comp_leftUnitor` and
  `Stacks.Perfect.SupportedFraction.whiskerLeft_globalSmul_unit_comp_rightUnitor`: multiplication
  by a global function on the monoidal unit, whiskered and then followed by a unit constraint, is
  the unit constraint followed by multiplication by that function.  These two are the only places
  where the tensor product is examined on sections, and they are what carries `det(a)` across the
  twist.
* `Stacks.Perfect.SupportedFraction.unitConormalWedge_wedge_ne_zero`: the wedge of
  `unitConormalWedge` is not the zero morphism.

## Implementation notes

**Why the twisted class is independent of the equations.**  Write `ω_f` for the wedge of the family
`f` and `c_f` for the untwisted map of Stacks 0G7Q read on `ℱ`.  Stacks 0G7S says
`c_f = det(a) · c_g` and the determinant transformation law says `ω_g = det(a) · ω_f`.  The twisted
map sends a functional `λ` on the determinant line to `c_f(λ(ω_f))`, so changing the family
multiplies the argument of `c` by `det(a)` and divides `c` by the same `det(a)`:

`c_g(λ(ω_g)) = c_g(det(a) · λ(ω_f)) = det(a) · c_g(λ(ω_f)) = c_f(λ(ω_f))`.

No invertibility of `det(a)` is used, and `ConormalWedge` has no analogue of
`ConormalDeterminantData.wedge_cancel`.

**The monoidal structure is seated at the `X.Modules` spelling.**  The monoidal structure used is
`Stacks.SheafOfModules.OnSpace.monoidal` of Stacks 01CA, whose section formulas for the
constraints on local pure tensors are what the two unitor lemmas are proved from.  It is seated
here as a `local instance` whose *type* is written `MonoidalCategory X.Modules`: the instance of
`OnSpaceMonoidal` is stated at the `SheafOfModules (structureSheafRing X.toRingedSpace)` spelling,
which is the same category by `rfl` but is not the discrimination key instance search uses for a
goal phrased with `X.Modules`, so the attribute form of the instance does not fire.

The same mismatch reaches inside the two unitor proofs, and that is why `mul_smul` is applied
there with both of its types given.  The section the unitor lemmas produce is a section of the
*transported* object, spelled through the `ULift` equivalence that `monoidal` is defined by, and
the scalar they multiply by lives in `X.toRingedSpace.presheaf.obj (op V)`; neither is the
spelling the module instance on `A.val.obj (op V)` is keyed at, which is
`X.ringCatSheaf.val.obj (op V)`.  Pinning `α` and `β` to that keyed spelling — the base ring of
`A` and the sections of `A`, both equal to what the goal says by `rfl` — is what lets the
existing `Module` instance be found instead of a new one being searched for at a spelling nothing
is registered at.

**The degenerate datum.**  `ConormalWedge X Z c` is inhabited by `line := 0` with `wedge := 0`,
for which both statements are about the zero morphism; `unitConormalWedge` is a datum whose wedge
is not zero.

**The source is `i_*i^*ℱ`, presented as a cokernel.**  As in Stacks 0G7S and in
`SupportedFractionNaturality`, `i_*i^*ℱ` is presented as the cokernel of
`(f₁, …, f_c) : ℱ^{⊕c} ⟶ ℱ`, which depends on the family `f`.  Two families therefore give
twisted maps with two *different* sources, and they are compared, exactly as the source compares
the untwisted maps, after composing with the canonical epimorphism out of `ℱ`.

## References

* [Stacks Project, Tag 0G7T](https://stacks.math.columbia.edu/tag/0G7T)
* [Stacks Project, Tag 0G7S](https://stacks.math.columbia.edu/tag/0G7S)
* [Stacks Project, Tag 0G7Q](https://stacks.math.columbia.edu/tag/0G7Q)
* [Stacks Project, Tag 0FNV](https://stacks.math.columbia.edu/tag/0FNV)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.SupportedComplexes
open Stacks.Perfect.CechDerivedSupport
open Stacks.Perfect.ExtendedAlternatingCech
open Stacks.Perfect.ExtendedAlternatingCech.Augmentation
open Stacks.SheafOfModules.OnSpace
open scoped AlgebraicGeometry

universe u

namespace Stacks.Perfect.SupportedFraction

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] AlgebraicGeometry.modulesMonoidal

variable {X : Scheme.{u}}

/-! ### Multiplication by a global function against the monoidal structure -/

/-- Multiplication by a global function commutes with every morphism of `𝒪_X`-modules: a
morphism of sheaves of modules is `𝒪_X`-linear, and on sections over an open the multiplication
is by the restriction of the function to that open. -/
public theorem globalSmul_naturality (r : Γ(X, ⊤)) {M N : X.Modules} (φ : M ⟶ N) :
    globalSmul r M ≫ φ = φ ≫ globalSmul r N := by
  ext V z
  simp [globalSmul_app]

/-- A two-step composite of morphisms of sheaves of modules, on a local section, with the two
one-step evaluations supplied as hypotheses instead of being rewritten with later.  This is the
two-step form of `Stacks.SheafOfModules.OnSpace.sheaf_comp3_app_apply_of` and it is needed for
the same reason: the module structures on the intermediate section stay the ones the composite
itself produces, where a `rw` has to re-find the pattern under the `ULift` transport that the
monoidal structure carries. -/
private theorem comp2_app_apply_of {A B C : X.Modules} (p : A ⟶ B) (q : B ⟶ C)
    (U : (Opens X.carrier)ᵒᵖ) (s : A.val.obj U)
    {b : B.val.obj U} (hb : (p.val.app U).hom s = b)
    {c : C.val.obj U} (hc : (q.val.app U).hom b = c) :
    ((p ≫ q).val.app U).hom s = c := by
  subst hb hc
  rfl

/-- **Multiplication by `r` on the monoidal unit, whiskered on the right and followed by the left
unit constraint, is the left unit constraint followed by multiplication by `r`.**  On a local pure
tensor `s ⊗ a` both sides are `r·s·a`. -/
public theorem whiskerRight_globalSmul_unit_comp_leftUnitor (r : Γ(X, ⊤)) (A : X.Modules) :
    (globalSmul r (𝟙_ X.Modules) ▷ A) ≫ (λ_ A).hom = (λ_ A).hom ≫ globalSmul r A := by
  refine Stacks.SheafOfModules.OnSpace.tensor_hom_ext X.toRingedSpace fun U s a => ?_
  obtain ⟨V⟩ := U
  refine Eq.trans (comp2_app_apply_of _ _ _ _
    (Stacks.SheafOfModules.OnSpace.whiskerRight_tmul X.toRingedSpace
      (globalSmul r (𝟙_ X.Modules)) A (op V) s a)
    (Stacks.SheafOfModules.OnSpace.leftUnitor_tmul X.toRingedSpace A (op V) _ a)) ?_
  refine Eq.trans ?_ (comp2_app_apply_of _ _ _ _
    (Stacks.SheafOfModules.OnSpace.leftUnitor_tmul X.toRingedSpace A (op V) _ a) rfl).symm
  exact mul_smul (α := (X.ringCatSheaf.val.obj (op V) : Type u))
    (β := (A.val.obj (op V) : Type u)) _ _ _

/-- **Multiplication by `r` on the monoidal unit, whiskered on the left and followed by the right
unit constraint, is the right unit constraint followed by multiplication by `r`.**  On a local
pure tensor `a ⊗ s` both sides are `r·s·a`. -/
public theorem whiskerLeft_globalSmul_unit_comp_rightUnitor (r : Γ(X, ⊤)) (A : X.Modules) :
    (A ◁ globalSmul r (𝟙_ X.Modules)) ≫ (ρ_ A).hom = (ρ_ A).hom ≫ globalSmul r A := by
  refine Stacks.SheafOfModules.OnSpace.tensor_hom_ext X.toRingedSpace fun U a s => ?_
  obtain ⟨V⟩ := U
  refine Eq.trans (comp2_app_apply_of _ _ _ _
    (Stacks.SheafOfModules.OnSpace.whiskerLeft_tmul X.toRingedSpace A
      (globalSmul r (𝟙_ X.Modules)) (op V) a s)
    (Stacks.SheafOfModules.OnSpace.rightUnitor_tmul X.toRingedSpace A (op V) a _)) ?_
  refine Eq.trans ?_ (comp2_app_apply_of _ _ _ _
    (Stacks.SheafOfModules.OnSpace.rightUnitor_tmul X.toRingedSpace A (op V) a _) rfl).symm
  exact mul_smul (α := (X.ringCatSheaf.val.obj (op V) : Type u))
    (β := (A.val.obj (op V) : Type u)) _ _ _

/-- The inverse right unit constraint carries multiplication by `r` to multiplication by `r` on
the unit, whiskered on the left. -/
public theorem rightUnitor_inv_comp_whiskerLeft_globalSmul_unit (r : Γ(X, ⊤)) (A : X.Modules) :
    (ρ_ A).inv ≫ (A ◁ globalSmul r (𝟙_ X.Modules)) = globalSmul r A ≫ (ρ_ A).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, ← whiskerLeft_globalSmul_unit_comp_rightUnitor r A,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- `whiskerRight_globalSmul_unit_comp_leftUnitor` with a trailing morphism, which is the shape
the composites below present. -/
public theorem whiskerRight_globalSmul_unit_comp_leftUnitor_assoc (r : Γ(X, ⊤)) (A : X.Modules)
    {B : X.Modules} (h : A ⟶ B) :
    (globalSmul r (𝟙_ X.Modules) ▷ A) ≫ (λ_ A).hom ≫ h =
      (λ_ A).hom ≫ globalSmul r A ≫ h := by
  rw [← Category.assoc, whiskerRight_globalSmul_unit_comp_leftUnitor, Category.assoc]

/-- `rightUnitor_inv_comp_whiskerLeft_globalSmul_unit` with a trailing morphism, which is the
shape the composites below present. -/
public theorem rightUnitor_inv_comp_whiskerLeft_globalSmul_unit_assoc (r : Γ(X, ⊤))
    (A : X.Modules) {B : X.Modules} (h : A ⊗ 𝟙_ X.Modules ⟶ B) :
    (ρ_ A).inv ≫ (A ◁ globalSmul r (𝟙_ X.Modules)) ≫ h =
      globalSmul r A ≫ (ρ_ A).inv ≫ h := by
  rw [← Category.assoc, rightUnitor_inv_comp_whiskerLeft_globalSmul_unit, Category.assoc]

/-! ### The wedge of the conormal classes of a family of equations, as data -/

/-- **A determinant datum for the families of `c` equations cutting out `Z`.**  A module `line`
on `X`, a global section of it — written as a morphism out of the monoidal unit — for every
family of `c` equations with zero locus `Z`, and the transformation law that changing the
equations by a matrix multiplies the section by the determinant of the matrix.  The motivating
example is `line = i_*⋀^c 𝒞_{Z/X}` with the wedge `[f₁] ∧ ⋯ ∧ [f_c]` of the conormal classes. -/
public structure ConormalWedge (X : Scheme.{u}) (Z : Set X) (c : ℕ) where
  /-- The determinant line. -/
  line : X.Modules
  /-- The section attached to a family of `c` equations cutting out `Z`. -/
  wedge (f : Fin c → Γ(X, ⊤)) (hf : equationsClosedSet f = Z) : 𝟙_ X.Modules ⟶ line
  /-- Changing the equations by a matrix multiplies the wedge by the determinant of the
  matrix. -/
  wedge_det (f g : Fin c → Γ(X, ⊤)) (hf : equationsClosedSet f = Z)
      (hg : equationsClosedSet g = Z) (a : Matrix (Fin c) (Fin c) Γ(X, ⊤))
      (ha : ∀ j, g j = ∑ i, a j i * f i) :
    wedge g hg = wedge f hf ≫ globalSmul a.det line

/-! ### Evaluation of the dual determinant line at a trivialization -/

/-- **The dual `L^∨ = SheafHom(L, 𝒪_X)` of an `𝒪_X`-module**, at the `X.Modules` spelling of the
category.  This is `Stacks.SheafOfModules.OnSpace.dualSheaf`, whose stated type is the
`SheafOfModules (structureSheafRing X.toRingedSpace)` spelling of the same category; the
ascription is what makes the monoidal structure seated above apply to it. -/
@[ega "0 4.1.5", sga "3 I 4.6.5.1", sga "3 III 0.6", sga "3 VIIA 4.3.3"]
public abbrev dualModule (L : X.Modules) : X.Modules := dualSheaf X.toRingedSpace L

/-- **The evaluation pairing `L^∨ ⊗ L ⟶ 𝒪_X`** of Stacks 0FNV, at the `X.Modules` spelling; see
`dualModule`. -/
public abbrev evalPairing (L : X.Modules) : dualModule L ⊗ L ⟶ 𝟙_ X.Modules :=
  evaluationTensor X.toRingedSpace L

/-- **Evaluation of the dual of a module at a global section of the module**, `L^∨ ⟶ 𝒪_X`.  It is
the inverse right unit constraint, the global section whiskered on the left, and the constructed
evaluation pairing of Stacks 0FNV. -/
public def evalWedge (L : X.Modules) (ω : 𝟙_ X.Modules ⟶ L) : dualModule L ⟶ 𝟙_ X.Modules :=
  (ρ_ (dualModule L)).inv ≫ (dualModule L ◁ ω) ≫ evalPairing L

/-- **Evaluation at `r·ω` is multiplication by `r` followed by evaluation at `ω`.**  This is the
step that carries the determinant across the twist. -/
public theorem evalWedge_comp_globalSmul (L : X.Modules) (ω : 𝟙_ X.Modules ⟶ L) (r : Γ(X, ⊤)) :
    evalWedge L (ω ≫ globalSmul r L) = globalSmul r (dualModule L) ≫ evalWedge L ω := by
  rw [evalWedge, evalWedge, ← globalSmul_naturality r ω, MonoidalCategory.whiskerLeft_comp,
    Category.assoc, rightUnitor_inv_comp_whiskerLeft_globalSmul_unit_assoc]

/-! ### The twisted class map -/

variable {Z : Set X}

/-- **The twisted fraction class** `line^∨ ⊗ i_*i^*ℱ ⟶ i_*ℋ^c_Z(ℱ)`: a local functional on the
line is evaluated at the wedge of the equations, and the resulting local section of `i_*i^*ℱ`
is sent into the local cohomology sheaf by the class map of Stacks 0G7Q.  The source `i_*i^*ℱ`
is presented as the cokernel of `(f₁, …, f_c)`, as Stacks 0G7Q presents it. -/
public def twistedFractionClass {d : ℕ} (D : ConormalWedge X Z (d + 1))
    (f : Fin (d + 1) → Γ(X, ⊤)) (hf : equationsClosedSet f = Z) (F : X.Modules)
    [F.IsQuasicoherent] {T : Set X} (hT : IsClosed T) (hTf : equationsClosedSet f ⊆ T) :
    dualModule D.line ⊗ cokernel (equationsMultiplication f F) ⟶
      supportCohomologySheaf hT F ((d + 1 : ℕ) : ℤ) :=
  (evalWedge D.line (D.wedge f hf) ▷ cokernel (equationsMultiplication f F)) ≫
    (λ_ (cokernel (equationsMultiplication f F))).hom ≫
      supportedFractionClass f F ≫ cokernelLastDifToSupport f F hT hTf

/-- **The twisted fraction class read on `line^∨ ⊗ ℱ`**, through the canonical
epimorphism `ℱ ↠ i_*i^*ℱ`.  This is the form in which the maps belonging to two different
families of equations can be compared, since the two presentations of `i_*i^*ℱ` are two different
objects; it is the same device Stacks 0G7S uses for the untwisted maps. -/
public def twistedFractionSource {d : ℕ} (D : ConormalWedge X Z (d + 1))
    (f : Fin (d + 1) → Γ(X, ⊤)) (hf : equationsClosedSet f = Z) (F : X.Modules)
    [F.IsQuasicoherent] {T : Set X} (hT : IsClosed T) (hTf : equationsClosedSet f ⊆ T) :
    dualModule D.line ⊗ F ⟶ supportCohomologySheaf hT F ((d + 1 : ℕ) : ℤ) :=
  (evalWedge D.line (D.wedge f hf) ▷ F) ≫ (λ_ F).hom ≫ supportedFractionSource f F hT hTf

/-- Whiskering `φ` on the left past the evaluation `e ▷ -` and the left unit constraint. -/
private theorem whiskerLeft_comp_whiskerRight_leftUnitor_comp {W F G H : X.Modules} (φ : F ⟶ G)
    (e : W ⟶ 𝟙_ X.Modules) (h : G ⟶ H) :
    (W ◁ φ) ≫ (e ▷ G) ≫ (λ_ G).hom ≫ h = (e ▷ F) ≫ (λ_ F).hom ≫ φ ≫ h := by
  rw [← Category.assoc, MonoidalCategory.whisker_exchange, Category.assoc,
    MonoidalCategory.leftUnitor_naturality_assoc]

/-- The map read on `line^∨ ⊗ ℱ` is the twisted fraction class composed with the canonical
epimorphism `ℱ ↠ i_*i^*ℱ`, twisted. -/
public theorem whiskerLeft_cokernelπ_comp_twistedFractionClass {d : ℕ}
    (D : ConormalWedge X Z (d + 1)) (f : Fin (d + 1) → Γ(X, ⊤)) (hf : equationsClosedSet f = Z)
    (F : X.Modules) [F.IsQuasicoherent] {T : Set X} (hT : IsClosed T)
    (hTf : equationsClosedSet f ⊆ T) :
    (dualModule D.line ◁ cokernel.π (equationsMultiplication f F)) ≫
        twistedFractionClass D f hf F hT hTf =
      twistedFractionSource D f hf F hT hTf := by
  rw [twistedFractionClass, twistedFractionSource, supportedFractionSource,
    whiskerLeft_comp_whiskerRight_leftUnitor_comp]

/-! ### Canonicity: the twisted map does not depend on the equations -/

/-- **The twisted fraction class does not depend on the family of equations.**  If two
families `f` and `g` of `c` equations cut out the same closed subset `Z` and are related by a
matrix `a`, then the two twisted maps `line^∨ ⊗ ℱ ⟶ i_*ℋ^c_Z(ℱ)` coincide: Stacks 0G7S says the
untwisted class maps differ by `det(a)`, and by the determinant law so do the two wedges. -/
public theorem twistedFractionSource_eq {d : ℕ} (D : ConormalWedge X Z (d + 1))
    (f g : Fin (d + 1) → Γ(X, ⊤)) (hf : equationsClosedSet f = Z) (hg : equationsClosedSet g = Z)
    (a : Matrix (Fin (d + 1)) (Fin (d + 1)) Γ(X, ⊤)) (ha : ∀ j, g j = ∑ i, a j i * f i)
    (F : X.Modules) [F.IsQuasicoherent] :
    twistedFractionSource D f hf F (isClosed_equationsClosedSet f) subset_rfl =
      twistedFractionSource D g hg F (isClosed_equationsClosedSet f) (hg.trans hf.symm).le := by
  rw [twistedFractionSource, twistedFractionSource,
    supportedFractionSource_eq_det_smul f g a F ha (hg.trans hf.symm),
    D.wedge_det f g hf hg a ha, evalWedge_comp_globalSmul,
    globalSmul_naturality a.det (evalWedge D.line (D.wedge f hf)),
    MonoidalCategory.comp_whiskerRight, Category.assoc,
    whiskerRight_globalSmul_unit_comp_leftUnitor_assoc]

/-! ### Functoriality in the coefficient module -/

/-- **The twisted fraction class is functorial in the quasi-coherent module `ℱ`.**  For every
morphism `φ : ℱ ⟶ 𝒢` of quasi-coherent `𝒪_X`-modules the square

`(line^∨ ⊗ φ) ≫ c_𝒢 = c_ℱ ≫ i_*ℋ^c_Z(φ)`

commutes, the right-hand factor being `supportCohomologySheafFunctor` on `φ`. -/
public theorem twistedFractionSource_natural {d : ℕ} (D : ConormalWedge X Z (d + 1))
    (f : Fin (d + 1) → Γ(X, ⊤)) (hf : equationsClosedSet f = Z) {F G : X.Modules}
    [F.IsQuasicoherent] [G.IsQuasicoherent] (φ : F ⟶ G) {T : Set X} (hT : IsClosed T)
    (hTf : equationsClosedSet f ⊆ T) :
    (dualModule D.line ◁ φ) ≫ twistedFractionSource D f hf G hT hTf =
      twistedFractionSource D f hf F hT hTf ≫
        (supportCohomologySheafFunctor hT ((d + 1 : ℕ) : ℤ)).map φ := by
  rw [twistedFractionSource, twistedFractionSource,
    whiskerLeft_comp_whiskerRight_leftUnitor_comp, supportedFractionSource_natural]
  exact (Category.assoc _ _ _).symm

/-! ### Named inhabitants of the datum

This section names the zero datum and a datum whose wedge is not zero. -/

/-- **Multiplication by a product of global functions is the composite of the two
multiplications.** -/
public theorem globalSmul_mul (r s : Γ(X, ⊤)) (M : X.Modules) :
    globalSmul (r * s) M = globalSmul r M ≫ globalSmul s M := by
  ext V z
  simp [globalSmul_app, mul_smul]

/-- **Multiplication by an invertible global function is an isomorphism**, the inverse being
multiplication by the inverse function. -/
public theorem isIso_globalSmul_of_isUnit {r : Γ(X, ⊤)} (hr : IsUnit r) (M : X.Modules) :
    IsIso (globalSmul r M) := by
  obtain ⟨v, rfl⟩ := hr
  have h1 : globalSmul (1 : Γ(X, ⊤)) M = 𝟙 M := by
    ext V z
    simp [globalSmul_app]
  refine ⟨globalSmul ((v⁻¹ : Γ(X, ⊤)ˣ) : Γ(X, ⊤)) M, ?_, ?_⟩
  · rw [← globalSmul_mul, v.mul_inv, h1]
  · rw [← globalSmul_mul, v.inv_mul, h1]

/-- **The degenerate inhabitant of `ConormalWedge`**: the zero wedge, which exists for every
`X`, every closed subset `Z` and every `c`; the wedge is the same morphism for every family. -/
public def zeroConormalWedge (X : Scheme.{u}) (Z : Set X) (c : ℕ) : ConormalWedge X Z c where
  line := 𝟙_ X.Modules
  wedge _ _ := 0
  wedge_det _ _ _ _ _ _ := zero_comp.symm

/-- **A non-degenerate inhabitant of `ConormalWedge` at `c = 1`**: the structure sheaf as the
line, with the wedge of the one-element family `f` taken to be multiplication by `f 0`.  The
determinant transformation law holds because for a `1 × 1` matrix the determinant is its single
entry, so `g 0 = a.det * f 0` is exactly the relation between the two families.

This is not the geometric conormal line of any closed immersion — the data `(X, Z, 1)` of these
statements does not determine one; see `ConormalWedge`.  Its purpose is to witness that the
binder `D : ConormalWedge X Z (d + 1)` is inhabited by something whose line is not a zero
object, so that `twistedFractionSource_eq` and `twistedFractionSource_natural` are not vacuous.
-/
public def unitConormalWedge (X : Scheme.{u}) (Z : Set X) : ConormalWedge X Z 1 where
  line := 𝟙_ X.Modules
  wedge f _ := globalSmul (f 0) (𝟙_ X.Modules)
  wedge_det f g hf hg a ha := by
    have h : g 0 = a.det * f 0 := by
      rw [Matrix.det_fin_one]
      simpa using ha 0
    rw [← globalSmul_mul, h]
    exact congrArg (fun t => globalSmul t (𝟙_ X.Modules)) (mul_comm a.det (f 0))

/-- The wedge of `unitConormalWedge` is multiplication by the single equation. -/
@[simp] public theorem unitConormalWedge_wedge {Z : Set X} (f : Fin 1 → Γ(X, ⊤))
    (hf : equationsClosedSet f = Z) :
    (unitConormalWedge X Z).wedge f hf = globalSmul (f 0) (𝟙_ X.Modules) :=
  rfl

/-- The line of `unitConormalWedge` is the structure sheaf. -/
@[simp] public theorem unitConormalWedge_line {Z : Set X} :
    (unitConormalWedge X Z).line = 𝟙_ X.Modules :=
  rfl

/-- **The monoidal unit of `X.Modules` is not a zero object** as soon as `X` carries a nonzero
global function: its module of sections over `⊤` is `Γ(X, 𝒪_X)` itself. -/
public theorem not_isZero_tensorUnit (X : Scheme.{u}) [Nontrivial Γ(X, (⊤ : X.Opens))] :
    ¬ IsZero (𝟙_ X.Modules) := by
  intro h
  have h1 : IsZero ((_root_.SheafOfModules.evaluation X.ringCatSheaf
      (op (⊤ : X.Opens))).obj (𝟙_ X.Modules)) :=
    Functor.map_isZero _ h
  exact not_subsingleton Γ(X, (⊤ : X.Opens)) (ModuleCat.isZero_iff_subsingleton.mp h1)

/-- **The wedge of `unitConormalWedge` is not the zero morphism**, for a family whose single
equation is invertible on a scheme with a nonzero global function.  Contrast
`zeroConormalWedge`, whose wedge is zero for every family: the binder
`D : ConormalWedge X Z (d + 1)` therefore separates the two statements above from the statements
about the zero morphism that the degenerate datum gives. -/
public theorem unitConormalWedge_wedge_ne_zero (X : Scheme.{u}) (Z : Set X)
    [Nontrivial Γ(X, (⊤ : X.Opens))] (f : Fin 1 → Γ(X, ⊤))
    (hf : equationsClosedSet f = Z) (hr : IsUnit (f 0)) :
    (unitConormalWedge X Z).wedge f hf ≠ 0 := by
  rw [unitConormalWedge_wedge]
  intro h0
  have hiso : IsIso (globalSmul (f 0) (𝟙_ X.Modules)) := isIso_globalSmul_of_isUnit hr _
  have hz : IsIso (0 : 𝟙_ X.Modules ⟶ 𝟙_ X.Modules) := h0 ▸ hiso
  refine not_isZero_tensorUnit X ((IsZero.iff_id_eq_zero _).2 ?_)
  calc 𝟙 (𝟙_ X.Modules)
      = (0 : 𝟙_ X.Modules ⟶ 𝟙_ X.Modules) ≫ inv (0 : 𝟙_ X.Modules ⟶ 𝟙_ X.Modules) :=
        (IsIso.hom_inv_id _).symm
    _ = 0 := zero_comp

end Stacks.Perfect.SupportedFraction

end
