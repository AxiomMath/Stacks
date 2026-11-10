module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPower
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerCoherence
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.FractionClassMap
public import StacksFrontier.AlgebraicGeometry.Picard.GaloisDescent.Pullback

/-!
# Endomorphisms of an invertible module, and `End(ℒ) = Γ(X, 𝒪_X)`

Let `ℒ` be an invertible sheaf of modules on a site with a sheaf of commutative rings `𝒪`. This
file proves that a nonzero endomorphism of `ℒ` is an isomorphism as soon as the same holds for
the structure sheaf, and — on a scheme whose ring of global functions is a field — that it holds
for the structure sheaf.

The two halves are independent.

*The invertible case reduces to the structure sheaf.* Tensoring by an invertible module is an
autoequivalence `T` of the category of modules ([Stacks, Tag 01CS], here
`Stacks.SheafOfModules.TensorPower.isEquivalence_tensorRightFunctor`) and `T(𝒪) ≅ ℒ`
(`Stacks.SheafOfModules.TensorPower.tensorPowerOneIso`, the first tensor power of
[Stacks, Tag 01CU]). An equivalence is fully faithful and therefore preserves and reflects both
zero morphisms and isomorphisms, so conjugating by that isomorphism identifies the
endomorphisms of `ℒ` with those of `𝒪` compatibly with being zero and with being invertible.

*On the structure sheaf an endomorphism is multiplication by a global function.* A morphism
`𝒪_X ⟶ M` of `𝒪_X`-modules is the same thing as a global section of `M`
(`CategoryTheory.SheafOfModules.unitHomEquiv`), and an endomorphism `χ` of `𝒪_X` is therefore
determined by the global function `r = χ(1)`: on sections over an open `U` it is
`x ↦ x · r|_U`, because `χ` is linear and `x = x · 1`. So `χ` is multiplication by `r`, which is
an isomorphism when `r` is a unit (`Stacks.Perfect.FractionClass.isIso_smulHom`), and `r` is a
unit as soon as it is nonzero and `Γ(X, 𝒪_X)` is a field.

## Main results

* `Stacks.InvertibleEndomorphism.isIso_of_ne_zero_of_isInvertible` — on any site, a nonzero
  endomorphism of an invertible module is an isomorphism provided every nonzero endomorphism of
  the structure sheaf is.
* `Stacks.InvertibleEndomorphism.isIso_endUnit_of_ne_zero` — on a scheme `X` with
  `Γ(X, 𝒪_X)` a field, a nonzero endomorphism of `𝒪_X` is an isomorphism.
* `Stacks.InvertibleEndomorphism.isIso_of_ne_zero_of_isInvertible_of_isField` — the two
  combined: on a scheme `X` with `Γ(X, 𝒪_X)` a field, a nonzero endomorphism of an invertible
  `𝒪_X`-module is an isomorphism.

## What is and is not proved

Everything here is proved outright; no hypothesis is carried and no result of the Stacks project
is assumed beyond what the library already has.

**No `@[stacks 0B40]` attribute is placed.** Part (5) of [Stacks, Tag 0B40] is about two
*different* invertible modules of *equal degree* on a proper integral curve over a field, and its
equality clause says that a nonzero map between them is an isomorphism. What is proved here is
the statement for a single invertible module — endomorphisms, not homomorphisms — on an arbitrary
scheme whose global functions form a field. That is neither the source's statement nor a clause
of it; part (5) itself is proved, as
`AlgebraicGeometry.invertibleCurveDegree_le_of_hom_ne_zero` and
`AlgebraicGeometry.isIso_of_invertibleCurveDegree_eq_of_hom_ne_zero`
(`StacksFrontier/AlgebraicGeometry/Variety/Curve/SectionDegree.lean`). The specialisation that *is*
needed by [Stacks, Tag 0C5R] — both modules isomorphic to the same twist `𝒪(d)` on `𝐏¹_k`, hence
the map an endomorphism of `𝒪(d)` after transport — is exactly what the results below cover.

## References

* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 0B40](https://stacks.math.columbia.edu/tag/0B40)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.SheafOfModules.TensorSheafification (structureSheaf structureRingPresheaf)
open Stacks.SheafOfModules (IsInvertible)
open Stacks.SheafOfModules.TensorPower (tensorPowerEquivalence tensorPowerOneIso)
open Stacks.Perfect.FractionClass (smulHom isIso_smulHom resTop smulHom_app_apply)
open Stacks.RingedSpace (structureIsSheaf)

universe u v w

namespace Stacks.InvertibleEndomorphism

/-! ### Reduction of the invertible case to the structure sheaf -/

section Site

variable {C : Type v} [Category.{w} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{u})
  (hO : Presheaf.IsSheaf J (structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]

/-- **A nonzero endomorphism of an invertible module is an isomorphism**, granted that a nonzero
endomorphism of the structure sheaf is.

Tensoring by `L` is an autoequivalence `T` of the category of `𝒪`-modules ([Stacks, Tag 01CS])
and `T(𝒪) ≅ L` is the first tensor power of [Stacks, Tag 01CU]. Conjugating `φ` by that
isomorphism and taking the preimage under `T` — which exists and is unique because an
equivalence is fully faithful — produces an endomorphism `χ` of `𝒪`; it is nonzero because a
full functor preserves zero morphisms and `φ` is recovered from `T(χ)` by conjugating back, and
it is then an isomorphism by hypothesis, whence so are `T(χ)` and `φ`. -/
public theorem isIso_of_ne_zero_of_isInvertible
    (hunit : ∀ χ : SheafOfModules.unit (structureSheaf O hO) ⟶
      SheafOfModules.unit (structureSheaf O hO), χ ≠ 0 → IsIso χ)
    (L : SheafOfModules.{u} (structureSheaf O hO)) [IsInvertible O hO L]
    (φ : L ⟶ L) (hφ : φ ≠ 0) : IsIso φ := by
  let T := (tensorPowerEquivalence O hO L 1).functor
  have e : T.obj (SheafOfModules.unit (structureSheaf O hO)) ≅ L := tensorPowerOneIso O hO L
  have hmap : T.map (T.preimage (e.hom ≫ φ ≫ e.inv)) = e.hom ≫ φ ≫ e.inv := T.map_preimage _
  have hconj : φ = e.inv ≫ (e.hom ≫ φ ≫ e.inv) ≫ e.hom := by simp
  have hχ0 : T.preimage (e.hom ≫ φ ≫ e.inv) ≠ 0 := by
    intro h0
    refine hφ ?_
    have hz : e.hom ≫ φ ≫ e.inv = 0 := by rw [← hmap, h0, Functor.map_zero]
    rw [hconj, hz]
    simp
  have := hunit _ hχ0
  have hiso : IsIso (e.hom ≫ φ ≫ e.inv) := by rw [← hmap]; infer_instance
  rw [hconj]
  infer_instance

end Site

/-! ### Endomorphisms of the structure sheaf of a scheme -/

/-- **A nonzero endomorphism of `𝒪_X` is an isomorphism when `Γ(X, 𝒪_X)` is a field.**

An endomorphism `χ` of `𝒪_X` corresponds under `CategoryTheory.SheafOfModules.unitHomEquiv` to
the global section `r = χ(1)`, and the compatibility of that section with restriction says
`χ(1)|_U = r|_U` over every open `U`; linearity then gives `χ(x) = x · r|_U`, so `χ` is
multiplication by `r`. If `r` were zero then `χ` would be multiplication by zero, hence zero; so
`r ≠ 0`, hence a unit, and multiplication by a unit global function is an isomorphism. -/
public theorem isIso_endUnit_of_ne_zero (X : Scheme.{u}) (hX : IsField Γ(X, ⊤))
    (χ : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf)
    (hχ : χ ≠ 0) : IsIso χ := by
  have hsmulzero : ∀ M : X.Modules, smulHom (0 : Γ(X, ⊤)) M = 0 := by
    intro M
    refine Scheme.Modules.hom_ext _ _ fun V => ?_
    refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun x => ?_)
    rw [smulHom_app_apply, map_zero, zero_smul]
    rfl
  set s := (SheafOfModules.unit X.ringCatSheaf).unitHomEquiv χ with hs
  set r : Γ(X, ⊤) := s.val (op ⊤) with hr
  have hnat : ∀ U : (TopologicalSpace.Opens ↥X)ᵒᵖ,
      (SheafOfModules.unit X.ringCatSheaf).val.map (homOfLE (le_top : U.unop ≤ ⊤)).op r =
        s.val U := fun U =>
    PresheafOfModules.sections_property s (homOfLE (le_top : U.unop ≤ ⊤)).op
  have hchi : χ = smulHom r (SheafOfModules.unit X.ringCatSheaf) := by
    refine (SheafOfModules.unit X.ringCatSheaf).unitHomEquiv.injective
      (Subtype.ext (funext fun U => ?_))
    change s.val U = resTop r U • (1 : X.ringCatSheaf.obj.obj U)
    rw [smul_eq_mul, mul_one, ← hnat U]
    rfl
  have hr0 : r ≠ 0 := by
    intro h0
    refine hχ ?_
    rw [hchi, h0]
    exact hsmulzero _
  obtain ⟨b, hb⟩ := hX.mul_inv_cancel hr0
  rw [hchi]
  exact isIso_smulHom (⟨⟨r, b, hb, (mul_comm b r).trans hb⟩, rfl⟩ : IsUnit r) _

/-- **A nonzero endomorphism of an invertible `𝒪_X`-module is an isomorphism when
`Γ(X, 𝒪_X)` is a field.** This is the two halves of the file put together; it is the form in
which the equality clause of part (5) of [Stacks, Tag 0B40] is used on the projective line, where
`Γ(𝐏¹_k, 𝒪) = k`. -/
public theorem isIso_of_ne_zero_of_isInvertible_of_isField (X : Scheme.{u})
    (hX : IsField Γ(X, ⊤))
    (L : SheafOfModules.{u} (structureSheaf X.toRingedSpace.presheaf
      (structureIsSheaf X.toRingedSpace)))
    (hL : IsInvertible X.toRingedSpace.presheaf (structureIsSheaf X.toRingedSpace) L)
    (φ : L ⟶ L) (hφ : φ ≠ 0) : IsIso φ :=
  have := hL
  isIso_of_ne_zero_of_isInvertible X.toRingedSpace.presheaf (structureIsSheaf X.toRingedSpace)
    (fun χ hχ => isIso_endUnit_of_ne_zero X hX χ hχ) L φ hφ

end Stacks.InvertibleEndomorphism

end
