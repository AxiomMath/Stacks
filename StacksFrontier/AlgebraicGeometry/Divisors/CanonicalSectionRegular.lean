module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LeftDualLocalDualBasis
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerCoherence
public import StacksFrontier.AlgebraicGeometry.Conormal.RestrictIdealSheaf
public import StacksFrontier.AlgebraicGeometry.Divisors.DivisorInvertibleSheaf
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.RegularSections
public import StacksFrontier.AlgebraicGeometry.InvertibleDual.Evaluation
public import StacksCore.Tactic.StacksAttribute

/-!
# The canonical section of the sheaf of an effective Cartier divisor is regular

Let `X` be a scheme and `D ⊆ X` an effective Cartier divisor. The canonical section `1_D` of
`𝒪_X(D) = SheafHom(ℐ_D, 𝒪_X)` is the ideal inclusion `ℐ_D ⟶ 𝒪_X` read as a global section of
the dual, and this file proves that it is a *regular* section: the morphism
`𝒪_X ⟶ 𝒪_X(D)` it determines is a monomorphism.

The argument is the one of the source read through the dual: tensoring with `ℐ_D` is an
autoequivalence, because `ℐ_D` is invertible, hence faithful, hence it reflects monomorphisms;
and the image of `1_D : 𝒪_X ⟶ ℐ_D^∨` under `- ⊗ ℐ_D`, composed with the left unitor and with the
evaluation pairing `ℐ_D^∨ ⊗ ℐ_D ≅ 𝒪_X`, is the ideal inclusion `ℐ_D ⟶ 𝒪_X`. That inclusion is a
`CategoryTheory.Limits.kernel.ι`, hence a monomorphism.

## Main results

* `Stacks.SheafOfModules.evaluation_unitHom_whiskerRight_val_app`: for any sheaf of modules `L`
  and any global section `s` of its dual `L^∨`, the composite
  `L ≅ 𝒪 ⊗ L --(ŝ ▷ L)--> L^∨ ⊗ L --ev--> 𝒪` acts on a local section `x` of `L` as `s` itself,
  that is, as `Stacks.SheafOfModules.evalSection`.
* `Stacks.Divisors.evaluation_canonicalHom`: the same composite at the canonical section of
  an effective Cartier divisor is the ideal inclusion `ℐ_D ⟶ 𝒪_X`.
* `Stacks.Divisors.canonicalSection_isRegular`: **the first clause of [Stacks, Tag 01X0]**.

## Implementation notes

**Why the dual is on the left.** `Stacks.SheafOfModules.evaluation` is the pairing
`L^∨ ⊗ L ⟶ 𝒪`, so the functor that has to be applied to `1_D` is `- ⊗ ℐ_D`, which is
`Stacks.SheafOfModules.TensorPower.tensorRightFunctor`. Taking it rather than
`Stacks.SheafOfModules.tensorLeftFunctor` avoids the braiding of the tensor product sheaf
entirely, so no braiding step has to be computed here. A description of the braiding on local
pure tensors does exist, should one ever be wanted:
`Stacks.SheafOfModules.braiding_tensorSectionsAt` and `tensorSheafBraiding_tensorSectionsAt` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/TensorSheafBraidingSections.lean` exchange the two
factors of a local pure tensor, at the `tensorSectionsAt` spelling of the construction this file
calls `tensorPt`.

**How the identification is computed.** `Stacks.SheafOfModules.tensorPt` is a *local pure
tensor*, the image under the Tag 05NA sheafification unit of a pure tensor of local sections,
and the three facts used are that the inverse left unitor produces one
(`leftUnitor_inv_eq_tensorPt`), that right whiskering acts on its first factor
(`tensorPt_whiskerRight`), and that the evaluation pairing reads it off as `evalSection`
(`evaluation_tensorPt`). All three are already in the library.

**The clause of Tag 01X0 proved here.** Tag 01X0 has three suffixed members in the census,
`canonical_section_regular`, `divisor_regular_section_equiv` and `regular_section_divisor`. The
first is `Stacks.Divisors.canonicalSection_isRegular` below; the other two are
`AlgebraicGeometry.existsUnique_invertibleSheafIso_zeroScheme` and
`AlgebraicGeometry.effectiveCartierDivisor_equiv_regularSectionClass`, in
`StacksFrontier/AlgebraicGeometry/Divisors/RegularSectionCorrespondence.lean`.

## References

* [Stacks Project, Tag 01X0](https://stacks.math.columbia.edu/tag/01X0)
* [Stacks Project, Tag 01WX](https://stacks.math.columbia.edu/tag/01WX)
* [Stacks Project, Tag 01WY](https://stacks.math.columbia.edu/tag/01WY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory TopologicalSpace Opposite
open AlgebraicGeometry
open Stacks.SheafOfModules.TensorSheafification (structureSheaf)

attribute [local instance] Stacks.SheafOfModules.Strict.monoidalCategory

universe v u

namespace Stacks.SheafOfModules

section General

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (𝒪 : Cᵒᵖ ⥤ CommRingCat.{max u v})
  (h𝒪 : Presheaf.IsSheaf J (TensorSheafification.structureRingPresheaf 𝒪))
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [HasWeakSheafify J AddCommGrpCat.{max u v}]
  (L : SheafOfModules.{max u v} (structureSheaf 𝒪 h𝒪))

/-- **Evaluating a global section of the dual through the evaluation pairing recovers the
section.** For `s` a global section of `L^∨`, write `ŝ : 𝒪 ⟶ L^∨` for the morphism it
determines. The composite

`L ≅ 𝒪 ⊗ L --(ŝ ▷ L)--> L^∨ ⊗ L --ev--> 𝒪`

sends a local section `x` of `L` to the value `Stacks.SheafOfModules.evalSection` of `s` on `x`.

This is the sections-level content of the evaluation pairing which the regularity of the
canonical section of an effective Cartier divisor rests on. -/
theorem evaluation_unitHom_whiskerRight_val_app
    (s : (dualSheaf 𝒪 h𝒪 L).sections) (V : Cᵒᵖ) (x : L.val.obj V) :
    ((λ_ L).inv ≫ ((dualSheaf 𝒪 h𝒪 L).unitHomEquiv.symm s ▷ L) ≫
        Stacks.SheafOfModules.evaluation 𝒪 h𝒪 L).val.app V x
      = evalSection 𝒪 L.val (SheafOfModules.unit (structureSheaf 𝒪 h𝒪)).val V (s.val V) x := by
  have hone : (((dualSheaf 𝒪 h𝒪 L).unitHomEquiv.symm s).val.app V).hom
      (1 : (structureSheaf 𝒪 h𝒪).obj.obj V) = s.val V :=
    (SheafOfModules.unitHomEquiv_apply_coe _ _ V).symm.trans
      (congrArg (fun t : (dualSheaf 𝒪 h𝒪 L).sections => t.val V)
        ((dualSheaf 𝒪 h𝒪 L).unitHomEquiv.apply_symm_apply s))
  have key : ∀ a : (structureSheaf 𝒪 h𝒪).obj.obj V,
      ((Stacks.SheafOfModules.evaluation 𝒪 h𝒪 L).val.app V).hom
          ((((dualSheaf 𝒪 h𝒪 L).unitHomEquiv.symm s ▷ L).val.app V).hom
            (tensorPt 𝒪 h𝒪 (𝟙_ (SheafOfModules.{max u v} (structureSheaf 𝒪 h𝒪))) L V a x))
        = evalSection 𝒪 L.val (SheafOfModules.unit (structureSheaf 𝒪 h𝒪)).val V
            ((((dualSheaf 𝒪 h𝒪 L).unitHomEquiv.symm s).val.app V).hom a) x := fun a =>
    (congrArg (fun z => ((Stacks.SheafOfModules.evaluation 𝒪 h𝒪 L).val.app V).hom z)
        (tensorPt_whiskerRight 𝒪 h𝒪 ((dualSheaf 𝒪 h𝒪 L).unitHomEquiv.symm s) V a x)).trans
      (evaluation_tensorPt 𝒪 h𝒪 L V _ x)
  exact (congrArg (fun tensorSection => ((Stacks.SheafOfModules.evaluation 𝒪 h𝒪 L).val.app V).hom
      ((((dualSheaf 𝒪 h𝒪 L).unitHomEquiv.symm s ▷ L).val.app V).hom tensorSection))
    (leftUnitor_inv_eq_tensorPt 𝒪 h𝒪 (A := L) V x)).trans
      ((key 1).trans (congrArg (fun t => evalSection 𝒪 L.val
        (SheafOfModules.unit (structureSheaf 𝒪 h𝒪)).val V t x) hone))

end General

end Stacks.SheafOfModules

namespace Stacks.Divisors

variable {X : Scheme.{u}} (D : X.IdealSheafData)

/-- The sheaf condition on the structure sheaf of a scheme, in the form which indexes the
monoidal structure of Tag 01CA on sheaves of modules. It is the same proposition as
`(structureSheafRing X.toRingedSpace).property`,
written so that instance search for the monoidal structure succeeds. -/
abbrev schemeIsSheaf (X : Scheme.{u}) := (structureSheafRing X.toRingedSpace).property

/-- The ideal sheaf `𝒪_X(-D) = ℐ_D`, read at the structure-sheaf index which the monoidal
structure on sheaves of modules is stated at. This is `Stacks.Divisors.negativeTwist'`; only the
spelling of its index differs. -/
noncomputable abbrev idealModule :
    SheafOfModules.{u} (structureSheaf X.presheaf (schemeIsSheaf X)) :=
  negativeTwist' D

/-- The morphism `𝒪_X ⟶ 𝒪_X(D)` determined by the canonical section `1_D`. -/
noncomputable abbrev canonicalHom :
    𝟙_ (SheafOfModules.{u} (structureSheaf X.presheaf (schemeIsSheaf X))) ⟶
      Stacks.SheafOfModules.dualSheaf X.presheaf (schemeIsSheaf X) (idealModule D) :=
  (Stacks.SheafOfModules.dualSheaf X.presheaf (schemeIsSheaf X)
    (idealModule D)).unitHomEquiv.symm (canonicalSection' D)

/-- **The evaluation pairing turns the canonical section of `𝒪_X(D)` back into the ideal
inclusion.** The composite

`ℐ_D ≅ 𝒪_X ⊗ ℐ_D --(1_D ▷ ℐ_D)--> 𝒪_X(D) ⊗ ℐ_D --ev--> 𝒪_X`

is the inclusion `ℐ_D ⟶ 𝒪_X` of the ideal sheaf. This holds because the component of the
canonical section over an open `U` is, by definition, the restriction of that inclusion to the
slice site over `U`, and `Stacks.SheafOfModules.evalSection` reads a section of the sheaf-hom at
the terminal object of that slice site. -/
theorem evaluation_canonicalHom :
    (λ_ (idealModule D)).inv ≫ (canonicalHom D ▷ idealModule D) ≫
        Stacks.SheafOfModules.evaluation X.presheaf (schemeIsSheaf X) (idealModule D)
      = Stacks.ClosedImmersion.idealSheafι D.subschemeι.toLRSHom.toShHom :=
  SheafOfModules.Hom.ext (PresheafOfModules.hom_ext fun V =>
    ModuleCat.hom_ext (LinearMap.ext fun x =>
      Stacks.SheafOfModules.evaluation_unitHom_whiskerRight_val_app X.presheaf
        (schemeIsSheaf X) (idealModule D) (canonicalSection' D) V x))

/-- **The first clause of [Stacks, Tag 01X0].** For `D ⊆ X` an effective Cartier divisor on a
scheme, the canonical section `1_D` of `𝒪_X(D)` is a regular section.

Tensoring with `ℐ_D` is an autoequivalence of the category of `𝒪_X`-modules, since `ℐ_D` is
invertible, so it is faithful and therefore reflects monomorphisms; and
`Stacks.Divisors.evaluation_canonicalHom` identifies the image of `1_D` under it, up to the left
unitor and the evaluation isomorphism, with the inclusion `ℐ_D ⟶ 𝒪_X`, which is a kernel
morphism and hence a monomorphism. -/
@[stacks 01X0 "canonical_section_regular"]
theorem canonicalSection_isRegular [IsEffectiveCartierDivisor D] :
    AlgebraicGeometry.IsRegularSection X.presheaf
      (structureSheafRing X.toRingedSpace).property (canonicalSection' D) := by
  have hinv : Stacks.SheafOfModules.IsInvertible X.presheaf (schemeIsSheaf X) (idealModule D) :=
    isTensorInvertible_negativeTwist D
  let : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).flip.obj
      (idealModule D)).IsEquivalence :=
    Stacks.SheafOfModules.TensorPower.isEquivalence_tensorRightFunctor X.presheaf
      (schemeIsSheaf X) (idealModule D)
  have hev : IsIso (Stacks.SheafOfModules.evaluation X.presheaf (schemeIsSheaf X)
      (idealModule D)) :=
    Stacks.SheafOfModules.Scheme.isIso_evaluation_of_isInvertible X (idealModule D)
  have hmono : Mono ((λ_ (idealModule D)).inv ≫ (canonicalHom D ▷ idealModule D) ≫
      Stacks.SheafOfModules.evaluation X.presheaf (schemeIsSheaf X) (idealModule D)) := by
    rw [evaluation_canonicalHom D]
    exact Stacks.ClosedImmersion.mono_idealSheafι _
  have hcomp : Mono ((canonicalHom D ▷ idealModule D) ≫
      Stacks.SheafOfModules.evaluation X.presheaf (schemeIsSheaf X) (idealModule D)) :=
    (mono_comp_iff_of_isIso (λ_ (idealModule D)).inv _).mp hmono
  have hw : Mono (canonicalHom D ▷ idealModule D) :=
    have := hcomp
    mono_of_mono _ (Stacks.SheafOfModules.evaluation X.presheaf (schemeIsSheaf X)
      (idealModule D))
  have hmap : Mono (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      X.sheaf).flip.obj (idealModule D)).map (canonicalHom D)) := by
    rw [show ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        X.sheaf).flip.obj (idealModule D)).map (canonicalHom D) =
        canonicalHom D ▷ idealModule D from
      (Stacks.SheafOfModules.whiskerRight_eq_sheafify_map X.presheaf (schemeIsSheaf X)
        (canonicalHom D) (idealModule D)).symm]
    exact hw
  exact (Functor.reflectsMonomorphisms_of_faithful
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      X.sheaf).flip.obj (idealModule D))).reflects _ hmap

end Stacks.Divisors

end
