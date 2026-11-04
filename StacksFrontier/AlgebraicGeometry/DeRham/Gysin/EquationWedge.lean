module

public import StacksFrontier.AlgebraicGeometry.DeRham.Complex.DifferentialForms

/-!
# Wedging relative differential forms with the differentials of a family of functions

Let `π : X ⟶ S` be a morphism of schemes and let `f₁, …, f_c ∈ Γ(X, 𝒪_X)`. Each `f_j` has a
relative differential `d f_j`, a degree-one section of the algebra `Ω^•_{X/S}` of relative
differential forms, and their ordered wedge `d f₁ ∧ ⋯ ∧ d f_c` is a global section of
`Ω^c_{X/S}`. Right multiplication by it is a morphism of sheaves of modules

`Ω^p_{X/S} ⟶ Ω^{p+c}_{X/S}`.

## Main definitions

* `SheafOfModules.GradedAlgebra.rightMul`: right multiplication by a global homogeneous section
  of a sheaf of graded algebras, as a morphism of sheaves of modules.
* `SheafOfModules.GradedAlgebra.prodDegOne`: the ordered product of `n` degree-one local sections
  of a sheaf of graded algebras.
* `AlgebraicGeometry.Scheme.Hom.exactOneForm`: the degree-one relative differential form `d b` of
  a local section `b` of the structure sheaf.
* `AlgebraicGeometry.Scheme.Hom.equationsWedge`: the ordered wedge `d f₁ ∧ ⋯ ∧ d f_c` of the
  relative differentials of a finite family of global functions, as a global section of
  `Ω^c_{X/S}`.
* `AlgebraicGeometry.Scheme.Hom.gysinWedgeHom`: right multiplication by that global section, as a
  morphism `Ω^p_{X/S} ⟶ Ω^{p+c}_{X/S}` of sheaves of modules.

## Main results

* `SheafOfModules.GradedAlgebra.rightMul_app_apply` and
  `SheafOfModules.GradedAlgebra.prodDegOne_map`: right multiplication is given on sections by the
  graded multiplication, and the ordered product of degree-one sections commutes with
  restriction.
* `AlgebraicGeometry.Scheme.Hom.exactOneForm_map`: the exact one-form of a local section commutes
  with restriction.
* `AlgebraicGeometry.Scheme.Hom.gysinWedgeHom_app_apply`: the value of `gysinWedgeHom` on a local
  section `ω` is the wedge of `ω` with `d f₁ ∧ ⋯ ∧ d f_c`. This equation determines the morphism,
  a morphism of sheaves of modules being its family of maps on sections.
* `AlgebraicGeometry.Scheme.Hom.gysinWedgeHom_empty_apply`: for the empty family of functions the
  morphism is multiplication by the unit of `Ω^•_{X/S}`, hence the identity up to the degree
  identification `p + 0 = p`.

## Implementation notes

The two graded-algebra constructions are stated for an arbitrary sheaf of graded algebras, not
for `Ω^•_{X/S}`. That is not generality for its own sake: a morphism of sheaves of modules built
directly at `Ω^•_{X/S}` cannot be elaborated as a structure literal, because
`AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms` ascribes the type `X.Modules`, whose
sheaf of rings is `X.ringCatSheaf`, while the graded multiplication of
`relativeDifferentialFormsAlgebra` is stated over
`Stacks.RingedSpace.structureRingSheaf X.toRingedSpace`. The two are definitionally equal but not
syntactically, and instance search for the module structure on sections sees only the syntactic
form. At an abstract `A : SheafOfModules.GradedAlgebra R` there is one spelling and the question
does not arise.

`d b` is the universal relative derivation of Tag 01US followed by the degree-one generator of
the exterior algebra, so `exactOneForm` is the morphism-of-schemes counterpart of
`AlgebraicGeometry.SheafOfModules.exactOne`.

`prodDegOne` recurses on the **right**, `z₀ ⋯ zₙ = (z₀ ⋯ zₙ₋₁) · zₙ`. The degree of the result is
then `(n : ℤ) + 1`, which is *definitionally* `((n + 1 : ℕ) : ℤ)`, so no degree transport appears
in the definition and none of the graded `HEq` laws is needed. This is the same reason
`Stacks.GradedAlgebra.homogeneousProd` recurses on the right while
`Stacks.GradedAlgebra.homogeneousProdLeft` carries a `Stacks.degCast`. That existing product is
not reused here because it is stated for `Stacks.GradedAlgebra` over a presheaf of *commutative*
rings, which `Ω^•_{X/S}` reaches only through
`SheafOfModules.GradedAlgebra.toPresheafGradedAlgebra`, reintroducing the spelling mismatch
above.

Right multiplication by a *global* section is what makes `rightMul` a morphism of sheaves of
modules rather than a family of maps on sections: linearity in the moving variable is
`Stacks.BilinearMap.map_smul_left` and compatibility with restriction is
`Stacks.BilinearMap.naturality` together with the restriction compatibility of a global section.
Degrees are integers, a sheaf of graded algebras being `ℤ`-graded; the family of functions is
indexed by `Fin c` with `c : ℕ`, and `(c : ℤ)` is the only cast.

The morphism `gysinWedgeHom` built here is the wedge factor of the Gysin formula of
[Stacks, Tag 0G83], `γ^p(ω) = c_{f₁,…,f_c}(ω̃|_Z) ∧ d f₁ ∧ ⋯ ∧ d f_c`: it goes between sheaves on
`X` and its codomain is `Ω^{p+c}_{X/S}`. The Gysin map itself, which descends the composite of
that factor with the canonical map `c_{f₁,…,f_c}` of [Stacks, Tag 0G7Q] along restriction to the
closed subscheme cut out by the functions, is `AlgebraicGeometry.Scheme.Hom.gysinMap`.

## References

* [Stacks Project, Tag 0G83](https://stacks.math.columbia.edu/tag/0G83)
* [Stacks Project, Tag 0G7Q](https://stacks.math.columbia.edu/tag/0G7Q)
* [Stacks Project, Tag 01US](https://stacks.math.columbia.edu/tag/01US)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace SheafOfModules.GradedAlgebra

variable {C : Type*} [Category* C] {J : GrothendieckTopology C} {R : Sheaf J RingCat}

/-- Right multiplication by a global section `δ` of the degree-`q` part of a sheaf of graded
algebras, as a morphism of sheaves of modules from the degree-`p` to the degree-`p + q` part. -/
def rightMul (A : SheafOfModules.GradedAlgebra R) (p q : ℤ) (δ : (A.piece q).sections) :
    A.piece p ⟶ A.piece (p + q) where
  val :=
    { app := fun U => ModuleCat.ofHom
        { toFun := fun a => (A.mul p q).app U a (δ.eval U)
          map_add' := fun a b => by simp
          map_smul' := fun r a => (A.mul p q).map_smul_left U r a (δ.eval U) }
      naturality := by
        intro U V h
        ext a
        change (A.mul p q).app V ((A.piece p).val.map h a) (δ.eval V) =
          (A.piece (p + q)).val.map h ((A.mul p q).app U a (δ.eval U))
        rw [(A.mul p q).naturality h, PresheafOfModules.sections_property δ h] }

/-- On a local section `a`, right multiplication by `δ` is the graded product of `a` with the
value of `δ`. -/
@[simp]
theorem rightMul_app_apply (A : SheafOfModules.GradedAlgebra R) (p q : ℤ)
    (δ : (A.piece q).sections) (U : Cᵒᵖ) (a : (A.piece p).val.obj U) :
    (A.rightMul p q δ).val.app U a = (A.mul p q).app U a (δ.eval U) :=
  rfl

/-- The ordered product `z₀ ⋯ zₙ₋₁` of `n` degree-one local sections of a sheaf of graded
algebras, a local section of the degree-`n` part. The empty product is the unit of the algebra
and each new factor is multiplied on the right. -/
def prodDegOne (A : SheafOfModules.GradedAlgebra R) (U : Cᵒᵖ) :
    (n : ℕ) → (Fin n → (A.piece 1).val.obj U) → (A.piece (n : ℤ)).val.obj U
  | 0, _ => A.one.eval U
  | n + 1, z =>
      (A.mul (n : ℤ) 1).app U (prodDegOne A U n fun i => z i.castSucc) (z (Fin.last n))

/-- The empty ordered product of degree-one sections is the unit of the algebra. -/
@[simp]
theorem prodDegOne_zero (A : SheafOfModules.GradedAlgebra R) (U : Cᵒᵖ)
    (z : Fin 0 → (A.piece 1).val.obj U) :
    A.prodDegOne U 0 z = A.one.eval U :=
  rfl

/-- The ordered product of `n + 1` degree-one sections is the product of the first `n` of them
multiplied on the right by the last. -/
@[simp]
theorem prodDegOne_succ (A : SheafOfModules.GradedAlgebra R) (U : Cᵒᵖ) (n : ℕ)
    (z : Fin (n + 1) → (A.piece 1).val.obj U) :
    A.prodDegOne U (n + 1) z =
      (A.mul (n : ℤ) 1).app U (A.prodDegOne U n fun i => z i.castSucc) (z (Fin.last n)) :=
  rfl

/-- The ordered product of degree-one local sections commutes with restriction. -/
theorem prodDegOne_map (A : SheafOfModules.GradedAlgebra R) {U V : Cᵒᵖ} (h : U ⟶ V) (n : ℕ)
    (z : Fin n → (A.piece 1).val.obj U) :
    (A.piece (n : ℤ)).val.map h (A.prodDegOne U n z) =
      A.prodDegOne V n fun i => (A.piece 1).val.map h (z i) := by
  induction n with
  | zero => exact PresheafOfModules.sections_property A.one h
  | succ n ih =>
      refine ((A.mul (n : ℤ) 1).naturality h
        (A.prodDegOne U n fun i => z i.castSucc) (z (Fin.last n))).trans ?_
      exact congrArg
        (fun y => (A.mul (n : ℤ) 1).app V y ((A.piece 1).val.map h (z (Fin.last n))))
        (ih fun i => z i.castSucc)

end SheafOfModules.GradedAlgebra

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}}

/-- The degree-one relative differential form `d b` of a local section `b` of the structure
sheaf: the universal relative derivation of `b`, read in the algebra of relative differential
forms. -/
def exactOneForm (π : X ⟶ S) (U : X.Opensᵒᵖ) (b : X.presheaf.obj U) :
    (relativeDifferentialForms π 1).val.obj U :=
  (Scheme.Modules.exteriorGenerator (relativeDifferentials π)).val.app U
    ((universalRelativeDerivation π).d b)

/-- The exact one-form of a local section commutes with restriction. -/
theorem exactOneForm_map (π : X ⟶ S) {U V : X.Opensᵒᵖ} (h : U ⟶ V) (b : X.presheaf.obj U) :
    (relativeDifferentialForms π 1).val.map h (exactOneForm π U b) =
      exactOneForm π V (X.presheaf.map h b) :=
  (CategoryTheory.congr_fun
        ((Scheme.Modules.exteriorGenerator (relativeDifferentials π)).val.naturality h)
        ((universalRelativeDerivation π).d b)).symm.trans
    (congrArg
      (fun y => ((Scheme.Modules.exteriorGenerator (relativeDifferentials π)).val.app V).hom y)
      ((universalRelativeDerivation π).d_map h b).symm)

/-- The ordered wedge `d f₁ ∧ ⋯ ∧ d f_c` of the relative differentials of a finite family of
global functions, as a global section of `Ω^c_{X/S}`. -/
def equationsWedge (π : X ⟶ S) {c : ℕ} (f : Fin c → Γ(X, ⊤)) :
    (relativeDifferentialForms π (c : ℤ)).sections :=
  PresheafOfModules.sectionsMk
    (fun U => (relativeDifferentialFormsAlgebra π).prodDegOne U c fun j =>
      exactOneForm π U (X.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op (f j)))
    (fun {U V} h => by
      refine ((relativeDifferentialFormsAlgebra π).prodDegOne_map h c _).trans
        (congrArg ((relativeDifferentialFormsAlgebra π).prodDegOne V c) (funext fun j => ?_))
      refine (exactOneForm_map π h _).trans (congrArg (exactOneForm π V) ?_)
      have hmor : (homOfLE (le_top : V.unop ≤ ⊤)) = h.unop ≫ homOfLE (le_top : U.unop ≤ ⊤) :=
        Subsingleton.elim _ _
      have happ := congrArg (fun g : V.unop ⟶ (⊤ : X.Opens) => (X.presheaf.map g.op).hom (f j))
        hmor
      simpa only [op_comp, Quiver.Hom.op_unop, Functor.map_comp, ConcreteCategory.comp_apply]
        using happ.symm)

/-- On an open `U`, the equation wedge is the ordered product of the exact one-forms of the
restrictions of the functions `f j` to `U`. -/
@[simp]
theorem equationsWedge_eval (π : X ⟶ S) {c : ℕ} (f : Fin c → Γ(X, ⊤)) (U : X.Opensᵒᵖ) :
    (equationsWedge π f).eval U =
      (relativeDifferentialFormsAlgebra π).prodDegOne U c fun j =>
        exactOneForm π U (X.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op (f j)) :=
  rfl

/-- Right multiplication by `d f₁ ∧ ⋯ ∧ d f_c`, as a morphism of sheaves of modules
`Ω^p_{X/S} ⟶ Ω^{p+c}_{X/S}`. This is the wedge factor of the Gysin formula of
[Stacks, Tag 0G83]. -/
def gysinWedgeHom (π : X ⟶ S) {c : ℕ} (f : Fin c → Γ(X, ⊤)) (p : ℤ) :
    relativeDifferentialForms π p ⟶ relativeDifferentialForms π (p + (c : ℤ)) :=
  (relativeDifferentialFormsAlgebra π).rightMul p (c : ℤ) (equationsWedge π f)

/-- On a local section `ω` of `Ω^p_{X/S}`, right multiplication by the equation wedge is the
wedge of `ω` with `d f₁ ∧ ⋯ ∧ d f_c`. -/
@[simp]
theorem gysinWedgeHom_app_apply (π : X ⟶ S) {c : ℕ} (f : Fin c → Γ(X, ⊤)) (p : ℤ)
    (U : X.Opensᵒᵖ) (ω : (relativeDifferentialForms π p).val.obj U) :
    (gysinWedgeHom π f p).val.app U ω =
      ((relativeDifferentialFormsAlgebra π).mul p (c : ℤ)).app U ω
        ((relativeDifferentialFormsAlgebra π).prodDegOne U c fun j =>
          exactOneForm π U (X.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op (f j))) :=
  rfl

/-- For the empty family of functions the wedge factor is multiplication by the unit of
`Ω^•_{X/S}`, hence the identity up to the degree identification `p + 0 = p`. -/
theorem gysinWedgeHom_empty_apply (π : X ⟶ S) (f : Fin 0 → Γ(X, ⊤)) (p : ℤ)
    (U : X.Opensᵒᵖ) (ω : (relativeDifferentialForms π p).val.obj U) :
    HEq ((gysinWedgeHom π f p).val.app U ω) ω :=
  (relativeDifferentialFormsAlgebra π).mul_one p U ω

end AlgebraicGeometry.Scheme.Hom

end
