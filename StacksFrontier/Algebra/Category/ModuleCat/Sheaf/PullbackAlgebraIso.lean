module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorAlgebraPullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorCanonical
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorExteriorSymmetricAlgebras
public import StacksFrontier.AlgebraicGeometry.PullbackTensor.StalkFormula
public import StacksCore.Tactic.StacksAttribute

/-!
# Pullback and the tensor algebra of a sheaf of modules

Let `f : X ⟶ Y` be a morphism of ringed spaces and let `F` be a sheaf of `𝒪_Y`-modules.
Stacks 01CI asserts `f^*T(F) = T(f^*F)`, and similarly for the exterior and symmetric algebras.
This file proves the **tensor-algebra** half, degreewise and on the underlying direct-sum sheaf,
by reducing it to Stacks 01CD — pullback commutes with the tensor product of sheaves of modules,
`Stacks.RingedSpace.comparisonIso` — together with the identification `f^*𝒪_Y = 𝒪_X`.

The degree-`n` piece of `T(F)` is the `n`-fold tensor power `F^{⊗ n}`
(`SheafOfModules.TensorExteriorSymmetricAlgebras.tensorPieceIso`), and `SheafOfModules.tensorPower`
is defined by the left-nested recursion `F^{⊗ 0} = 𝒪`, `F^{⊗ 1} = F`,
`F^{⊗ (n+2)} = F ⊗ F^{⊗ (n+1)}`. So `f^*(F^{⊗ n}) ≅ (f^*F)^{⊗ n}` follows by induction from
01CD at the single pair `(F, F^{⊗ (n+1)})` at each step, with the structure sheaf as the base
case. No reassociation of tensor products occurs, so no coherence of 01CD with the associator is
needed — which matters, because none is available (see the implementation notes).

## Main definitions

* `Stacks.PullbackAlgebra.unitComparison` and `pullbackUnitIso`: the comparison
  `f^*𝒪_Y ⟶ 𝒪_X` of sheaves of modules and the fact that it is an isomorphism.
* `Stacks.PullbackAlgebra.tensorPow` and `Algebras`: `SheafOfModules.tensorPower` and
  `SheafOfModules.TensorExteriorSymmetricAlgebras` specialized to the site of open subsets of a
  ringed space.
* `Stacks.PullbackAlgebra.pullbackTensorPowStep` and `pullbackTensorPowIso`: one step of, and
  then the whole of, the comparison `f^*(F^{⊗ n}) ≅ (f^*F)^{⊗ n}`.
* `Stacks.PullbackAlgebra.pullbackTensorPieceIso` and `pullbackTensorSheafIso`: **Stacks 01CI for
  the tensor algebra**, degreewise and on the underlying direct-sum sheaf.

## Main results

* `Stacks.PullbackAlgebra.final_opensMap`: the inverse-image functor `f⁻¹ : Opens Y ⥤ Opens X` is
  final. This is what makes Mathlib's `SheafOfModules.pullbackObjUnitToUnit` invertible, hence
  what gives `f^*𝒪_Y = 𝒪_X`.
* `Stacks.PullbackAlgebra.pullbackUnitIso_hom_pullbackUnit`: the structure-sheaf comparison
  carries the pullback-unit image of `a ∈ 𝒪_Y(U)` to `f^♯(a) ∈ 𝒪_X(f⁻¹U)`.
* `Stacks.PullbackAlgebra.pullbackTensorPowStep_hom_unit_tmul` and
  `pullbackTensorPowIso_hom_unit_tmul`: **the section formula that pins the tensor-power
  comparison down.** On the pullback-unit image of the sheafification-unit image of `s ⊗ x` the
  degree-`n+2` comparison is the pure tensor of the pullback-unit image of `s` with the
  degree-`n+1` comparison applied to the pullback-unit image of `x`. Together with the degree-zero
  and degree-one values this determines the comparison on a family of local sections that
  generates, which is what makes the isomorphism *canonical* rather than merely existent.
* `Stacks.PullbackAlgebra.pullbackTensorPieceIso_generator`: the degree-one component carries the
  pullback of the degree-one generator of `T(F)` to the degree-one generator of `T(f^*F)`.
* `Stacks.PullbackAlgebra.pullbackTensorPieceIso_unit`: the degree-zero component carries the
  pullback of the unit of `T(F)` to the unit of `T(f^*F)`.
* `Stacks.PullbackAlgebra.pullbackTensorSheafIso_ι`: the direct-sum comparison restricts on each
  homogeneous summand to the degreewise comparison.

## Implementation notes

**What the tag covers, and what it does not.** The two `@[stacks 01CI]` declarations are about the
tensor algebra only. Neither the exterior nor the symmetric algebra is treated, and this is a
genuine mathematical gap rather than an omission:

* `SheafOfModules.TensorExteriorSymmetricAlgebras` records `⋀ⁿF` and `SymⁿF` only through the
  universal property of the whole graded algebra — there is no presentation of `⋀ⁿF` or `SymⁿF`
  in terms of tensor powers, so the induction above has no analogue for them.
  `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PowerPresentationSequences` builds the two maps of
  the Stacks 01CJ sequences but proves neither exactness nor epimorphy, so it cannot supply one.
* The route through the universal property instead — build a graded-algebra structure on `f^*A`
  and invert `SheafOfModules.GradedAlgebra.pullbackComparison` by initiality of `⋀(f^*F)` — needs
  the multiplication `f^*(A_i) ⊗ f^*(A_j) ⟶ f^*(A_{i+j})` obtained by conjugating `A`'s
  multiplication with 01CD, and then needs its **associativity**, i.e. compatibility of the 01CD
  comparison with the associator of the tensor product of sheaves of modules. That compatibility
  is not proved anywhere: `modulePullback` is not known to be a monoidal functor. The exterior
  case needs one further input, that square-zero-ness of the pulled-back generator on *all* local
  sections of `f^*F` follows from square-zero-ness on the pullback-unit images, i.e. that those
  images generate `f^*F` locally.

**Why the two comparison isomorphisms are used through names rather than inlined.**
`unitComparison` here, and `Stacks.RingedSpace.pullbackTensorIsoApp` in the 01CD file, are each
`asIso` of a morphism that already has an `IsIso` instance, so both look like they could be
written out at the point of use. They cannot: at a point of use the isomorphism's *type* is
wanted in the folded spelling that the consumer has —
`(pullbackFunctor f).obj (tensorPow Y F (n + 2))` rather than
the pullback of the native tensor of `F` with `tensorPow Y F (n + 1)`, which are
definitionally but not syntactically equal — and then the instance argument of `asIso` is sought
against a goal that still carries a metavariable and the synthesis fails. Naming the morphism
first, at its own type, and letting the folded spelling be reached by the defeq check of `:=`, is
what makes `pullbackTensorPowStep` elaborate. This is the same spelling discipline as elsewhere in
this directory: ascribe, do not rewrite.

**Two instances are restated here to short-circuit instance search, not because they are
missing.** `hasColimitsOfShape_discrete_nat` and `preservesColimitsOfShape_pullbackFunctor` are
each one application of an existing instance.
They are needed because importing
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorCanonical` — the 01CD file — enlarges
the instance set enough that `HasCoproduct (fun n : ℕ => A.piece n)` and
`PreservesColimit (Discrete.functor _) (modulePullback f)` exceed the default
`synthInstance.maxHeartbeats`, even though both are found without that import (for instance in
`ExteriorAlgebraPullback.lean`, which states the same coproducts). Naming the one-step
instantiations fixes that without raising any limit.

**Two opened namespaces supply the `IsIso (comparison f A B)` instance.**
`Stacks.PullbackTensor` and `Stacks.RingedSpace` each provide one — the two routes to Stacks
01CD — and both namespaces are opened here. That needs nothing: `IsIso` is a `Prop`, so
whichever instance search picks, the two are interchangeable by proof irrelevance.

**Universes.** Everything is at a single universe `u`, because `modulePullback` is: the
ringed-space pullback of sheaves of modules is only available at `RingedSpace.{u, u}` with modules
in `u`. `SheafOfModules.tensorPower` and `TensorExteriorSymmetricAlgebras` are stated over an
arbitrary site with the site universes independent of the module universe; the specializations
`tensorPow` and `Algebras` collapse them, and that is forced by `modulePullback`, not chosen.

**The degree is kept a variable.** `pullbackTensorPowIso` is defined by recursion and every lemma
about it quantifies over the degree; the two literal degrees that appear (`0` and `1`) appear only
as instantiations of already-elaborated statements.

## References

* [Stacks Project, Tag 01CI](https://stacks.math.columbia.edu/tag/01CI)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry
open RingedSpaceModuleAdjunction Stacks.RingedSpace Stacks.PullbackTensor

open scoped TensorProduct

universe u

namespace Stacks.PullbackAlgebra

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-! ### Finality of the inverse-image functor on open subsets -/

/-- The inverse-image functor `f⁻¹ : Opens Y ⥤ Opens X` on open subsets is final. -/
instance final_opensMap : (opensMap f).Final where
  out V := by
    let top : StructuredArrow V (opensMap f) :=
      StructuredArrow.mk (Y := (⊤ : Opens Y.carrier)) (homOfLE (by simp))
    have hto : ∀ j : StructuredArrow V (opensMap f), j ⟶ top := fun j =>
      StructuredArrow.homMk (homOfLE le_top) (Subsingleton.elim _ _)
    have : Nonempty (StructuredArrow V (opensMap f)) := ⟨top⟩
    exact zigzag_isConnected fun j₁ j₂ =>
      (Relation.ReflTransGen.single (Zag.of_hom (hto j₁))).tail (Zag.of_inv (hto j₂))

/-- Countable direct sums of sheaves of modules on a ringed space, as a one-step instance. -/
instance hasColimitsOfShape_discrete_nat (Z : RingedSpace.{u, u}) :
    HasColimitsOfShape (Discrete ℕ) (SheafOfModules.{u} (structureRingSheaf Z)) :=
  SheafOfModules.instHasColimitsOfShapeOfPresheafOfModulesObjFunctorOppositeRingCatIsSheaf
    (structureRingSheaf Z) (Discrete ℕ)

/-- Pullback preserves small-shape colimits, as a one-step instance. -/
noncomputable instance preservesColimitsOfShape_pullbackFunctor (K : Type) [Category.{0} K] :
    PreservesColimitsOfShape K (pullbackFunctor f) :=
  (modulePullbackPushforwardAdjunction f).leftAdjoint_preservesColimits.preservesColimitsOfShape

/-! ### Pullback of the structure sheaf -/

/-- The pullback of the structure sheaf of `Y`, read as a module over itself, is the structure
sheaf of `X`. -/
noncomputable def unitComparison :
    (pullbackFunctor f).obj (SheafOfModules.unit (structureRingSheaf Y)) ⟶
      SheafOfModules.unit (structureRingSheaf X) :=
  SheafOfModules.pullbackObjUnitToUnit (structureSheafHom f)

/-- The comparison `unitComparison f` is an isomorphism. -/
instance isIso_unitComparison : IsIso (unitComparison f) :=
  SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal (structureSheafHom f)

/-- The pullback of the structure sheaf of `Y`, read as a module over itself, is the structure
sheaf of `X`. -/
noncomputable def pullbackUnitIso :
    (pullbackFunctor f).obj (SheafOfModules.unit (structureRingSheaf Y)) ≅
      SheafOfModules.unit (structureRingSheaf X) :=
  asIso (unitComparison f)

/-- The forward map of `pullbackUnitIso f` is `unitComparison f`. -/
@[simp]
theorem pullbackUnitIso_hom : (pullbackUnitIso f).hom = unitComparison f := rfl

/-- The structure-sheaf comparison on local sections: it carries the pullback-unit image of a
section `a` of `𝒪_Y` to the image of `a` under the structure morphism of `f`. -/
theorem pullbackUnitIso_hom_pullbackUnit (U : (Opens Y.carrier)ᵒᵖ)
    (a : (structureRingSheaf Y).obj.obj U) :
    (pullbackUnitIso f).hom.val.app ((opensMap f).op.obj U)
        (pullbackUnit f (SheafOfModules.unit (structureRingSheaf Y)) U a) =
      sharp f U a :=
  (SheafOfModules.GradedAlgebra.homEquiv_symm_val_app_unit f
      (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom f)) U a).trans
    (SheafOfModules.unitToPushforwardObjUnit_val_app_apply (structureSheafHom f) a)

/-! ### Tensor powers -/

/-- The `n`-fold tensor power of a sheaf of modules on a ringed space. -/
noncomputable abbrev tensorPow (Z : RingedSpace.{u, u})
    (M : SheafOfModules.{u} (structureRingSheaf Z)) (n : ℕ) :
    SheafOfModules.{u} (structureRingSheaf Z) :=
  SheafOfModules.tensorPower (Opens.grothendieckTopology Z.carrier) (Osharp := Z.sheaf) M n

variable (F : SheafOfModules.{u} (structureRingSheaf Y))

/-- One step of the tensor-power comparison: the canonical comparison of Stacks 01CD at the
pair `(F, F^{⊗ n+1})`, followed by the comparison in degree `n+1` tensored on the left by
`f^*F`. -/
noncomputable def pullbackTensorPowStep (n : ℕ)
    (e : (pullbackFunctor f).obj (tensorPow Y F (n + 1)) ≅
      tensorPow X ((pullbackFunctor f).obj F) (n + 1)) :
    (pullbackFunctor f).obj (tensorPow Y F (n + 2)) ≅
      tensorPow X ((pullbackFunctor f).obj F) (n + 2) :=
  pullbackTensorIsoApp f F (tensorPow Y F (n + 1)) ≪≫
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨X.presheaf, X.IsSheaf⟩).obj ((pullbackFunctor f).obj F)).mapIso
        (X := (pullbackFunctor f).obj (tensorPow Y F (n + 1)))
        (Y := tensorPow X ((pullbackFunctor f).obj F) (n + 1)) e

/-- On the pullback-unit image of the sheafification-unit image of `s ⊗ x`, the step
`pullbackTensorPowStep f F n e` is the pure tensor of the pullback-unit image of `s` with `e`
applied to the pullback-unit image of `x`. -/
theorem pullbackTensorPowStep_hom_unit_tmul (n : ℕ)
    (e : (pullbackFunctor f).obj (tensorPow Y F (n + 1)) ≅
      tensorPow X ((pullbackFunctor f).obj F) (n + 1))
    (U : (Opens Y.carrier)ᵒᵖ) (s : F.val.obj U)
    (x : (tensorPow Y F (n + 1)).val.obj U) :
    (pullbackTensorPowStep f F n e).hom.val.app ((opensMap f).op.obj U)
        (pullbackUnit f (tensorPow Y F (n + 2)) U
          (((PresheafOfModules.sheafificationAdjunction.{u, u, u, u}
            (R := Stacks.SheafOfModules.Tensor.ringSheaf ⟨Y.presheaf, Y.IsSheaf⟩)
            (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf ⟨Y.presheaf, Y.IsSheaf⟩).obj)).unit.app
              (_root_.PresheafOfModules.tensorObj F.val (tensorPow Y F (n + 1)).val)).app U
                (s ⊗ₜ x))) =
      ((PresheafOfModules.sheafificationAdjunction.{u, u, u, u}
        (R := Stacks.SheafOfModules.Tensor.ringSheaf ⟨X.presheaf, X.IsSheaf⟩)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf ⟨X.presheaf, X.IsSheaf⟩).obj)).unit.app
          (_root_.PresheafOfModules.tensorObj ((pullbackFunctor f).obj F).val
            (tensorPow X ((pullbackFunctor f).obj F) (n + 1)).val)).app ((opensMap f).op.obj U)
        (pullbackUnit f F U s ⊗ₜ
          e.hom.val.app ((opensMap f).op.obj U)
            (pullbackUnit f (tensorPow Y F (n + 1)) U x)) := by
  rw [show (pullbackTensorPowStep f F n e).hom = comparison f F (tensorPow Y F (n + 1)) ≫ _
    from rfl]
  erw [_root_.SheafOfModules.comp_val, PresheafOfModules.comp_app, ConcreteCategory.comp_apply,
    comparison_pullbackUnit_unit_tmul]
  have mapIdentity :
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨X.presheaf, X.IsSheaf⟩).map (𝟙 ((pullbackFunctor f).obj F))).app
          ((pullbackFunctor f).obj (tensorPow Y F (n + 1))) ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨X.presheaf, X.IsSheaf⟩).obj ((pullbackFunctor f).obj F)).map e.hom =
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨X.presheaf, X.IsSheaf⟩).obj ((pullbackFunctor f).obj F)).map e.hom :=
    (congrArg (fun transformation ↦
      transformation.app ((pullbackFunctor f).obj (tensorPow Y F (n + 1))) ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨X.presheaf, X.IsSheaf⟩).obj ((pullbackFunctor f).obj F)).map e.hom)
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨X.presheaf, X.IsSheaf⟩).map_id ((pullbackFunctor f).obj F))).trans (Category.id_comp _)
  exact (_root_.SheafOfModules.hom_congr_app_apply mapIdentity
    ((opensMap f).op.obj U) _).symm.trans
    (tensorSheaf_map_unit_tmul X (𝟙 ((pullbackFunctor f).obj F)) e.hom
      ((opensMap f).op.obj U) (pullbackUnit f F U s)
      (pullbackUnit f (tensorPow Y F (n + 1)) U x))

/-- **Pullback commutes with tensor powers.** The comparison is built by recursion on the
degree: in degree zero it is the structure-sheaf comparison `pullbackUnitIso`, in degree one it
is the identity, and each further step is `pullbackTensorPowStep`. -/
noncomputable def pullbackTensorPowIso :
    (n : ℕ) → (pullbackFunctor f).obj (tensorPow Y F n) ≅
      tensorPow X ((pullbackFunctor f).obj F) n
  | 0 => pullbackUnitIso f
  | 1 => Iso.refl _
  | n + 2 => pullbackTensorPowStep f F n (pullbackTensorPowIso (n + 1))

/-- In degree zero the tensor-power comparison is `pullbackUnitIso f`. -/
@[simp]
theorem pullbackTensorPowIso_zero : pullbackTensorPowIso f F 0 = pullbackUnitIso f := rfl

/-- In degree one the tensor-power comparison is the identity. -/
@[simp]
theorem pullbackTensorPowIso_one : pullbackTensorPowIso f F 1 = Iso.refl _ := rfl

/-- In degree `n + 2` the tensor-power comparison is `pullbackTensorPowStep` applied to the
comparison in degree `n + 1`. -/
@[simp]
theorem pullbackTensorPowIso_succ_succ (n : ℕ) :
    pullbackTensorPowIso f F (n + 2) =
      pullbackTensorPowStep f F n (pullbackTensorPowIso f F (n + 1)) := rfl

/-- On the pullback-unit image of the sheafification-unit image of `s ⊗ x`, the degree-`n + 2`
tensor-power comparison is the pure tensor of the pullback-unit image of `s` with the
degree-`n + 1` comparison applied to the pullback-unit image of `x`. -/
theorem pullbackTensorPowIso_hom_unit_tmul (n : ℕ) (U : (Opens Y.carrier)ᵒᵖ)
    (s : F.val.obj U) (x : (tensorPow Y F (n + 1)).val.obj U) :
    (pullbackTensorPowIso f F (n + 2)).hom.val.app ((opensMap f).op.obj U)
        (pullbackUnit f (tensorPow Y F (n + 2)) U
          (((PresheafOfModules.sheafificationAdjunction.{u, u, u, u}
            (R := Stacks.SheafOfModules.Tensor.ringSheaf ⟨Y.presheaf, Y.IsSheaf⟩)
            (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf ⟨Y.presheaf, Y.IsSheaf⟩).obj)).unit.app
              (_root_.PresheafOfModules.tensorObj F.val (tensorPow Y F (n + 1)).val)).app U
                (s ⊗ₜ x))) =
      ((PresheafOfModules.sheafificationAdjunction.{u, u, u, u}
        (R := Stacks.SheafOfModules.Tensor.ringSheaf ⟨X.presheaf, X.IsSheaf⟩)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf ⟨X.presheaf, X.IsSheaf⟩).obj)).unit.app
          (_root_.PresheafOfModules.tensorObj ((pullbackFunctor f).obj F).val
            (tensorPow X ((pullbackFunctor f).obj F) (n + 1)).val)).app ((opensMap f).op.obj U)
        (pullbackUnit f F U s ⊗ₜ
          (pullbackTensorPowIso f F (n + 1)).hom.val.app ((opensMap f).op.obj U)
            (pullbackUnit f (tensorPow Y F (n + 1)) U x)) :=
  pullbackTensorPowStep_hom_unit_tmul f F n (pullbackTensorPowIso f F (n + 1)) U s x

/-! ### The tensor algebra -/

/-- The tensor, exterior and symmetric algebras of a sheaf of modules on a ringed space. -/
noncomputable abbrev Algebras (Z : RingedSpace.{u, u})
    (M : SheafOfModules.{u} (structureRingSheaf Z)) :=
  SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology Z.carrier) (Osharp := Z.sheaf) M

variable (S : Algebras Y F) (T : Algebras X ((pullbackFunctor f).obj F))

/-- The pullback of the degree-`n` piece of the tensor algebra of `F` is the degree-`n` piece of
the tensor algebra of `f^*F`. -/
@[stacks 01CI "the tensor algebra only. The exterior and symmetric algebras are NOT proved \
here; see the implementation notes for the two missing inputs."]
noncomputable def pullbackTensorPieceIso (n : ℕ) :
    (pullbackFunctor f).obj (S.tensor.piece (n : ℤ)) ≅ T.tensor.piece (n : ℤ) :=
  (pullbackFunctor f).mapIso (S.tensorPieceIso n) ≪≫ pullbackTensorPowIso f F n ≪≫
    (T.tensorPieceIso n).symm

/-- The forward map of `pullbackTensorPieceIso` is the pullback of the identification of the
degree-`n` piece of `T(F)` with `F^{⊗ n}`, followed by `pullbackTensorPowIso f F n` and the
identification of `(f^*F)^{⊗ n}` with the degree-`n` piece of `T(f^*F)`. -/
theorem pullbackTensorPieceIso_hom (n : ℕ) :
    (pullbackTensorPieceIso f F S T n).hom =
      (pullbackFunctor f).map (S.tensorPieceIso n).hom ≫
        (pullbackTensorPowIso f F n).hom ≫ (T.tensorPieceIso n).inv := rfl

/-- On the pullback-unit image of a local section, the degree-`n` comparison is the comparison
`pullbackTensorPowIso` of the identified section, followed by the identification of
`(f^*F)^{⊗ n}` with the degree-`n` piece of `T(f^*F)`. -/
private theorem pullbackTensorPieceIso_hom_pullbackUnit (n : ℕ) (U : (Opens Y.carrier)ᵒᵖ)
    (z : (S.tensor.piece (n : ℤ)).val.obj U) :
    (pullbackTensorPieceIso f F S T n).hom.val.app ((opensMap f).op.obj U)
        (pullbackUnit f (S.tensor.piece (n : ℤ)) U z) =
      (T.tensorPieceIso n).inv.val.app ((opensMap f).op.obj U)
        ((pullbackTensorPowIso f F n).hom.val.app ((opensMap f).op.obj U)
          (pullbackUnit f (tensorPow Y F n) U ((S.tensorPieceIso n).hom.val.app U z))) :=
  congrArg ((T.tensorPieceIso n).inv.val.app ((opensMap f).op.obj U))
    (congrArg ((pullbackTensorPowIso f F n).hom.val.app ((opensMap f).op.obj U))
      (pullbackUnit_naturality f (S.tensorPieceIso n).hom U z))

/-- The degree-one component of the comparison carries the pullback-unit image of the
degree-one generator of `T(F)` to the degree-one generator of `T(f^*F)` evaluated on the
pullback-unit image. -/
theorem pullbackTensorPieceIso_generator (U : (Opens Y.carrier)ᵒᵖ) (s : F.val.obj U) :
    (pullbackTensorPieceIso f F S T 1).hom.val.app ((opensMap f).op.obj U)
        (pullbackUnit f (S.tensor.piece 1) U (S.tensorGenerator.val.app U s)) =
      T.tensorGenerator.val.app ((opensMap f).op.obj U) (pullbackUnit f F U s) := by
  have hS : (S.tensorPieceIso 1).hom.val.app U (S.tensorGenerator.val.app U s) = s :=
    _root_.SheafOfModules.hom_congr_app_apply S.tensorPieceIso_one U s
  have hT : T.tensorGenerator = (T.tensorPieceIso 1).inv :=
    (Iso.comp_hom_eq_id (T.tensorPieceIso 1)).mp T.tensorPieceIso_one
  rw [hT]
  refine (pullbackTensorPieceIso_hom_pullbackUnit f F S T 1 U _).trans ?_
  rw [hS]
  rfl

/-- The degree-zero component of the comparison carries the pullback of the unit of `T(F)` to
the unit of `T(f^*F)`. -/
theorem pullbackTensorPieceIso_unit (U : (Opens Y.carrier)ᵒᵖ) :
    (pullbackTensorPieceIso f F S T 0).hom.val.app ((opensMap f).op.obj U)
        (pullbackUnit f (S.tensor.piece 0) U (S.tensor.one.eval U)) =
      T.tensor.one.eval ((opensMap f).op.obj U) := by
  refine (pullbackTensorPieceIso_hom_pullbackUnit f F S T 0 U _).trans ?_
  refine Eq.trans ?_ (_root_.SheafOfModules.iso_inv_hom_app_apply (T.tensorPieceIso 0) _
    (T.tensor.one.eval ((opensMap f).op.obj U)))
  refine congrArg ((T.tensorPieceIso 0).inv.val.app ((opensMap f).op.obj U)) ?_
  rw [T.tensorPieceIso_zero ((opensMap f).op.obj U), pullbackTensorPowIso_zero,
    S.tensorPieceIso_zero U]
  refine (pullbackUnitIso_hom_pullbackUnit f U 1).trans ?_
  exact map_one (ConcreteCategory.hom ((structureSheafHom f).hom.app U))

/-- The pullback of the underlying direct-sum sheaf of the tensor algebra of `F` is the
underlying direct-sum sheaf of the tensor algebra of `f^*F`. -/
@[stacks 01CI "the tensor algebra only, on the underlying direct-sum sheaf. The exterior and \
symmetric algebras are NOT proved here."]
noncomputable def pullbackTensorSheafIso :
    (pullbackFunctor f).obj S.tensorAlgebraSheaf ≅ T.tensorAlgebraSheaf :=
  PreservesCoproduct.iso (pullbackFunctor f) (fun n : ℕ => S.tensor.piece (n : ℤ)) ≪≫
    Sigma.mapIso fun n : ℕ => pullbackTensorPieceIso f F S T n

/-- The direct-sum comparison restricts on each homogeneous summand to the degreewise
comparison. -/
theorem pullbackTensorSheafIso_ι (n : ℕ) :
    (pullbackFunctor f).map (Sigma.ι (fun m : ℕ => S.tensor.piece (m : ℤ)) n) ≫
        (pullbackTensorSheafIso f F S T).hom =
      (pullbackTensorPieceIso f F S T n).hom ≫
        Sigma.ι (fun m : ℕ => T.tensor.piece (m : ℤ)) n := by
  have h : (pullbackFunctor f).map (Sigma.ι (fun m : ℕ => S.tensor.piece (m : ℤ)) n) ≫
        (PreservesCoproduct.iso (pullbackFunctor f)
          fun m : ℕ => S.tensor.piece (m : ℤ)).hom =
      Sigma.ι (fun m : ℕ => (pullbackFunctor f).obj (S.tensor.piece (m : ℤ))) n :=
    IsColimit.comp_coconePointUniqueUpToIso_hom
      (isColimitOfHasCoproductOfPreservesColimit (pullbackFunctor f)
        fun m : ℕ => S.tensor.piece (m : ℤ))
      (colimit.isColimit _) (Discrete.mk n)
  rw [pullbackTensorSheafIso, Iso.trans_hom, ← Category.assoc, h]
  simp

end Stacks.PullbackAlgebra

end
