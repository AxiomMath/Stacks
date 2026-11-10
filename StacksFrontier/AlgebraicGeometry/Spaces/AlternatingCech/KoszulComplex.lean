module

public import Mathlib.Algebra.Homology.Single
public import Mathlib.CategoryTheory.Sites.Abelian
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.AlternatingCech.ExteriorPower
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleTensor

/-!
# The Koszul complex of an object of the spaces-étale site of an algebraic space

Let `X` be an algebraic space over a scheme `S` and let `U` be an algebraic space étale over
`X`, that is an object of the spaces-étale site of `X`.  Writing `j_{U!} ℤ` for the extension
by zero of the constant sheaf of integers, the trace `j_{U!} ℤ ⟶ ℤ` sums the coefficients of a
local section, and the exterior powers `K^p = ∧^{p+1} j_{U!} ℤ` form a complex `K^•` whose
differential contracts by the trace.  Augmenting it by the trace in degree `0` gives the map
`K^• ⟶ ℤ[0]` of Stacks 0723.

## Main definitions

* `AlgebraicGeometry.Space.SpacesEtale.freeAbelianRepresentableTrace` is the trace of the free
  abelian presheaf on `U`, the sum of the coefficients.
* `AlgebraicGeometry.Space.SpacesEtale.koszulComplex` is the complex `K^•`, with
  `K^p = ∧^{p+1} j_{U!} ℤ` in degree `p` and the contraction by the trace as differential.
* `AlgebraicGeometry.Space.SpacesEtale.constantIntSheaf` is the constant sheaf `ℤ` on the
  spaces-étale site of `X`.

## Main results

* `AlgebraicGeometry.Space.SpacesEtale.koszulAugmentation` is **Stacks 0723**, the map
  `K^• ⟶ ℤ[0]`.
* `AlgebraicGeometry.Space.SpacesEtale.koszulComplexXZeroIso`: the term of `K^•` in degree `0`
  is `j_{U!} ℤ`, and `AlgebraicGeometry.Space.SpacesEtale.koszulAugmentation_f_zero_eq`
  identifies the augmentation in degree `0` with the trace.

## Implementation notes

`j_{U!} ℤ` is the sheafification of the free abelian presheaf on the representable presheaf of
`U`, by `AlgebraicGeometry.Space.SpacesEtale.extensionByZeroConstantFreeRepresentableIso`, and
the exterior powers of an abelian sheaf are the sheafifications of the objectwise exterior
powers of that presentation.  Working with the presentation is what makes the differential
available: the trace is the sum of coefficients, which on the free abelian presheaf is an
honest integral linear form on each group of sections, so the differential is the contraction
of `AddCommGrpCat.presheafKoszulDiff`, whereas on the sheaf `j_{U!} ℤ` itself the trace of a
local section is a locally constant integer rather than an integer.

Surjectivity of `U ⟶ X` is not needed for the complex or its augmentation; it is what makes
the augmentation a quasi-isomorphism, which is
`AlgebraicGeometry.Space.SpacesEtale.koszulAugmentation_quasiIso` in
`StacksFrontier.AlgebraicGeometry.Spaces.AlternatingCech.KoszulResolution`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space.SpacesEtale

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

/-! ### The trace of the free abelian presheaf -/

/-- The free abelian presheaf on the representable presheaf of an object `U` of the
spaces-étale site of `X`.  Its sheafification is `j_{U!} ℤ`. -/
abbrev freeAbelianRepresentablePresheaf (U : SpacesEtale B S hS X) :
    (SpacesEtale B S hS X)ᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  yoneda.obj U ⋙ AddCommGrpCat.free

/-- Reindexing a formal integral combination along a map of index types does not change the
sum of its coefficients. -/
theorem lift_one_comp_freeAbelianGroupMap {α β : Type*} (g : α → β) (x : FreeAbelianGroup α) :
    FreeAbelianGroup.lift (fun _ : β => (ULift.up 1 : ULift.{u + 1} ℤ))
        (FreeAbelianGroup.map g x) =
      FreeAbelianGroup.lift (fun _ : α => (ULift.up 1 : ULift.{u + 1} ℤ)) x := by
  induction x using FreeAbelianGroup.induction_on with
  | zero => simp
  | of a => simp
  | neg y hy => simp
  | add y z hy hz => simpa using congrArg₂ (· + ·) hy hz

/-- The trace of the free abelian presheaf on `U`: the sum of the coefficients of a formal
integral combination of morphisms into `U`. -/
def freeAbelianRepresentableTrace (U : SpacesEtale B S hS X) :
    freeAbelianRepresentablePresheaf B S hS X U ⟶
      AddCommGrpCat.constantInt.{u + 1} (SpacesEtale B S hS X) where
  app V := AddCommGrpCat.ofHom (FreeAbelianGroup.lift fun _ => (ULift.up 1 : ULift.{u + 1} ℤ))
  naturality {V W} f := by
    ext x
    exact lift_one_comp_freeAbelianGroupMap (fun g => f.unop ≫ g) x

/-- The trace of a generator of the free abelian presheaf on `U`, namely of a morphism
`V ⟶ U`, is `1`. -/
@[simp]
theorem presheafDual_freeAbelianRepresentableTrace_of (U : SpacesEtale B S hS X)
    (V : (SpacesEtale B S hS X)ᵒᵖ) (φ : (yoneda.obj U).obj V) :
    AddCommGrpCat.presheafDual (freeAbelianRepresentableTrace B S hS X U) V
        (FreeAbelianGroup.of φ) = 1 := by
  change (ULift.moduleEquiv (R := ℤ) (M := ℤ))
      (FreeAbelianGroup.lift (fun _ => (ULift.up 1 : ULift.{u + 1} ℤ))
        (FreeAbelianGroup.of φ)) = 1
  rw [FreeAbelianGroup.lift_apply_of]
  rfl

/-- The Koszul differential of the free abelian presheaf on `U` sends a wedge of generators
`φ_0 ∧ ⋯ ∧ φ_p` to the alternating sum over `i` of the wedges with `φ_i` omitted: this is the
differential of the Koszul complex of Stacks 0723. -/
theorem presheafKoszulDiff_freeAbelianRepresentableTrace_ιMulti (U : SpacesEtale B S hS X)
    (p : ℕ) (V : (SpacesEtale B S hS X)ᵒᵖ) (φ : Fin (p + 1) → (yoneda.obj U).obj V) :
    ((AddCommGrpCat.presheafKoszulDiff (freeAbelianRepresentableTrace B S hS X U) p).app V).hom
        (exteriorPower.ιMulti ℤ (p + 1) fun i => FreeAbelianGroup.of (φ i)) =
      ∑ i : Fin (p + 1), (-1 : ℤ) ^ (i : ℕ) • exteriorPower.ιMulti ℤ p
        fun j => FreeAbelianGroup.of (φ (i.succAbove j)) := by
  refine (exteriorPower.contract_ιMulti _ p _).trans (Finset.sum_congr rfl fun i _ => ?_)
  rw [presheafDual_freeAbelianRepresentableTrace_of, mul_one]
  rfl

/-! ### The complex `K^•` and its augmentation -/

/-- The constant sheaf `ℤ` on the spaces-étale site of `X`. -/
abbrev constantIntSheaf : Sheaf (topology B S hS X) AddCommGrpCat.{u + 1} :=
  (constantSheaf (topology B S hS X) AddCommGrpCat.{u + 1}).obj
    (AddCommGrpCat.of (ULift.{u + 1} ℤ))

/-- The complex `K^•` attached to an object `U` of the spaces-étale site of `X`: its term in
degree `p` is `K^p = ∧^{p+1} j_{U!} ℤ`, the sheafification of the `(p+1)`-st objectwise
exterior power of the free abelian presheaf on `U`, and its differential is the contraction by
the trace. -/
def koszulComplex (U : SpacesEtale B S hS X) :
    ChainComplex (Sheaf (topology B S hS X) AddCommGrpCat.{u + 1}) ℕ :=
  ((presheafToSheaf (topology B S hS X) AddCommGrpCat.{u + 1}).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj
    (AddCommGrpCat.presheafKoszul (freeAbelianRepresentableTrace B S hS X U))

/-- The term of `K^•` in degree `p` is the sheafified `(p+1)`-st exterior power. -/
theorem koszulComplex_X (U : SpacesEtale B S hS X) (p : ℕ) :
    (koszulComplex B S hS X U).X p =
      (presheafToSheaf (topology B S hS X) AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.presheafExteriorPower (freeAbelianRepresentablePresheaf B S hS X U)
          (p + 1)) :=
  rfl

/-- The differential of `K^•` is the sheafification of the contraction by the trace. -/
theorem koszulComplex_d (U : SpacesEtale B S hS X) (p : ℕ) :
    (koszulComplex B S hS X U).d (p + 1) p =
      (presheafToSheaf (topology B S hS X) AddCommGrpCat.{u + 1}).map
        (AddCommGrpCat.presheafKoszulDiff (freeAbelianRepresentableTrace B S hS X U) (p + 1)) :=
  congrArg (fun k => (presheafToSheaf (topology B S hS X) AddCommGrpCat.{u + 1}).map k)
    (AddCommGrpCat.presheafKoszul_d (freeAbelianRepresentableTrace B S hS X U) p)

/-- The term of `K^•` in degree `0` is `K^0 = ∧^1 j_{U!} ℤ = j_{U!} ℤ`. -/
def koszulComplexXZeroIso (U : SpacesEtale B S hS X) :
    (koszulComplex B S hS X U).X 0 ≅ extensionByZeroConstant B S hS X U :=
  (presheafToSheaf (topology B S hS X) AddCommGrpCat.{u + 1}).mapIso
      (AddCommGrpCat.presheafExteriorPowerOne (freeAbelianRepresentablePresheaf B S hS X U)) ≪≫
    (extensionByZeroConstantFreeRepresentableIso B S hS X U).symm

/-- The trace `K^0 ⟶ ℤ`, the sheafification of the sum of coefficients read on `∧^1`. -/
def koszulTrace (U : SpacesEtale B S hS X) :
    (koszulComplex B S hS X U).X 0 ⟶ constantIntSheaf B S hS X :=
  (presheafToSheaf (topology B S hS X) AddCommGrpCat.{u + 1}).map
    (AddCommGrpCat.presheafKoszulAugmentation (freeAbelianRepresentableTrace B S hS X U))

/-- The first differential of `K^•` followed by the trace vanishes. -/
theorem koszulComplex_d_comp_koszulTrace (U : SpacesEtale B S hS X) :
    (koszulComplex B S hS X U).d 1 0 ≫ koszulTrace B S hS X U = 0 := by
  erw [koszulComplex_d B S hS X U 0, koszulTrace, ← Functor.map_comp,
    AddCommGrpCat.presheafKoszulDiff_comp_presheafKoszulAugmentation]
  exact Functor.map_zero _ _ _

/-- **Stacks 0723.** The augmentation `K^• ⟶ ℤ[0]` of the complex `K^•` attached to an object
of the spaces-étale site of `X`: the trace in degree `0` and zero in higher degrees. -/
@[stacks 0723 "the augmentation K^• ⟶ ℤ[0]"]
def koszulAugmentation (U : SpacesEtale B S hS X) :
    koszulComplex B S hS X U ⟶
      (ChainComplex.single₀ (Sheaf (topology B S hS X) AddCommGrpCat.{u + 1})).obj
        (constantIntSheaf B S hS X) :=
  (ChainComplex.toSingle₀Equiv _ _).symm
    ⟨koszulTrace B S hS X U, koszulComplex_d_comp_koszulTrace B S hS X U⟩

/-- The augmentation `K^• ⟶ ℤ[0]` is the trace in degree `0`. -/
@[simp]
theorem koszulAugmentation_f_zero_eq (U : SpacesEtale B S hS X) :
    (koszulAugmentation B S hS X U).f 0 = koszulTrace B S hS X U :=
  ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _

end AlgebraicGeometry.Space.SpacesEtale

end
