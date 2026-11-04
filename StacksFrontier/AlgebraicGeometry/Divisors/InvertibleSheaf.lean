module

public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier
public import StacksFrontier.AlgebraicGeometry.InvertibleBridge.Basic
public import StacksFrontier.AlgebraicGeometry.InvertibleDual.Evaluation
public import StacksFrontier.AlgebraicGeometry.InvertibleQuotient.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHom
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerCoherence

/-!
# The invertible sheaf of an effective Cartier divisor

Let `S` be a scheme and `D ⊆ S` an effective Cartier divisor, with ideal sheaf `ℐ_D`. Tag 01WX
defines the invertible sheaf

`𝒪_S(D) = SheafHom(ℐ_D, 𝒪_S) = ℐ_D^{⊗ -1}`,

its canonical global section `1_D` — the one corresponding to the inclusion `ℐ_D ⟶ 𝒪_S` — the
negative twist `𝒪_S(-D) = 𝒪_S(D)^{⊗ -1} = ℐ_D`, and the difference twist
`𝒪_S(D - D') = 𝒪_S(D) ⊗_{𝒪_S} 𝒪_S(-D')`.

Every one of these objects was already formable from existing machinery, and the expression
`SheafHom(ℐ_D, 𝒪_S)` is used **unconditionally** inside
`Stacks.Divisors.normalSheafIsoInvertibleSheaf` and
`Stacks.Divisors.normalSheafIsoInvertibleSheaf_eval`, the two declarations carrying Tag 0B3P's
normal-sheaf clauses, written out there because this tag had no formalization. What this file
adds is the name, the two tensor-power identifications that the tag's chain of equalities
asserts, the canonical section with the characterisation that pins it to the ideal inclusion,
and the invertibility that the tag's own wording ("the invertible sheaf `𝒪_S(D)`") claims.

## Main definitions

* `Stacks.Divisors.negativeTwist`: `𝒪_S(-D)`, which *is* the ideal sheaf `ℐ_D`.
* `Stacks.Divisors.idealInclusion`: the inclusion `ℐ_D ⟶ 𝒪_S`, the kernel inclusion of the
  surjection `𝒪_S ⟶ 𝒪_D`.
* `Stacks.Divisors.invertibleSheaf`: `𝒪_S(D) = SheafHom(ℐ_D, 𝒪_S)`.
* `Stacks.Divisors.canonicalSection`: the canonical global section `1_D` of `𝒪_S(D)`.
* `Stacks.Divisors.differenceTwist`: `𝒪_S(D - D') = 𝒪_S(D) ⊗ 𝒪_S(-D')`.
* `Stacks.Divisors.invertibleSheafPairing` and `Stacks.Divisors.invertibleSheafPairing'`: the
  evaluation pairings `𝒪_S(D) ⊗ ℐ_D ≅ 𝒪_S` and `ℐ_D ⊗ 𝒪_S(D) ≅ 𝒪_S`. They are what normalizes
  the two identifications below, and they are the input a statement about addition of divisors
  in the Picard group (Tag 02OP) consumes.

## Main results

* `Stacks.Divisors.isInvertible_invertibleSheaf`: `𝒪_S(D)` is invertible.
* `Stacks.Divisors.invertibleSheafIsoNegativeTensorPower`: `𝒪_S(D) ≅ ℐ_D^{⊗ -1}`, the second
  equality of Tag 01WX (1).
* `Stacks.Divisors.negativeTwistIsoNegativeTensorPower`: `𝒪_S(-D) ≅ 𝒪_S(D)^{⊗ -1}`, the first
  equality of Tag 01WX (3).
* `Stacks.Divisors.evalSection_canonicalSection`: the canonical section, evaluated on a section
  of `ℐ_D` over the whole of `S`, is that section's image under the inclusion `ℐ_D ⟶ 𝒪_S`. This
  is what "the global section corresponding to the inclusion mapping" asserts; without it the
  correspondence would live only in a docstring.

## Implementation notes

**The definitions carry no divisor hypothesis; the identifications do.** `SheafHom(ℐ_D, 𝒪_S)`,
the ideal inclusion and the canonical section are formable for an arbitrary closed subscheme,
and the existing uses of the expression form them that way, so they are defined here with no
`IsEffectiveCartierDivisor` binder — a generalization of the tag, not a weakening of it. The
hypothesis appears exactly where the source needs it: in the invertibility of `𝒪_S(D)` and in
the two identifications with tensor powers, which are meaningless without it since the powers
are indexed by the autoequivalence that invertibility provides.

**Invertibility of the dual needs no trivializing cover as a hypothesis.**
`Stacks.SheafOfModules.Invertible.isInvertible_dualSheaf_of_dualBasisOne` proves it from a
rank-one dual basis on a covering family, and that was for a while the only form available; the
missing step, the converse half of Tag 0B8M, has since been proved and joined, so
`Stacks.SheafOfModules.Scheme.isIso_evaluation_of_isInvertible` gives the evaluation pairing of
*any* invertible module sheaf on a scheme. With that pairing in hand, invertibility of
`𝒪_S(D)` is Tag 0B8K (2) ⟹ (1) — `Stacks.SheafOfModules.isInvertible_of_tensorIsoUnit` — and no
dual basis is constructed anywhere here.

**Which `IsInvertible`.** `Stacks.Divisors.IsEffectiveCartierDivisor` is stated with
`AlgebraicGeometry.SheafOfModules.IsInvertible`, and so is the tensor-power development of Tag
01CU; the evaluation pairing is stated with `Stacks.SheafOfModules.IsInvertible`. Both
directions are crossed with `Stacks.InvertibleBridge`, the canonical interface, and nothing is
restated on either side. `isInvertible_invertibleSheaf` is declared for the
`AlgebraicGeometry` copy, because that is the one the tensor powers in the statements below
need at elaboration time; the other copy follows from it by the same bridge.

**Why the spellings are crossed by `have`.** The structure sheaf of a scheme is written
`X.sheaf.obj` by `IsEffectiveCartierDivisor` and `X.presheaf` by the evaluation pairing, and
the sheaf of rings `structureSheafRing X.toRingedSpace` by the former and
`structureSheafRing X.toRingedSpace` by the latter.
  Each pair is equal by `rfl`,
but instance search is syntactic, so the witness is moved between the spellings by a `have`
ascribed at the shape the consumer wants. The public statements here all use the
`X.sheaf.obj` / `structureSheafRing` spelling, which is the one the other occurrences of this
expression already use.

**The canonical section is a section over `⊤`.** A section of `SheafHom(ℐ_D, 𝒪_S)` over an open
`U` is, by Tag 03EM, a morphism `ℐ_D|_U ⟶ 𝒪_S|_U` of presheaves of modules on the slice site,
so the global section corresponding to the inclusion is the restriction of that inclusion to
the slice site over `⊤`, and `Stacks.SheafOfModules.evalSection` evaluates it. The
characterisation is a `rfl`.

## References

* [Stacks Project, Tag 01WX](https://stacks.math.columbia.edu/tag/01WX)
* [Stacks Project, Tag 01WR](https://stacks.math.columbia.edu/tag/01WR)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 0B8K](https://stacks.math.columbia.edu/tag/0B8K)
* [Stacks Project, Tag 0FNV](https://stacks.math.columbia.edu/tag/0FNV)
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction (structureSheafHom)

universe u

namespace Stacks.Divisors

variable {X : Scheme.{u}} (D D' : X.IdealSheafData)

/-- **Stacks Project, Tag 01WX (3).** The sheaf `𝒪_S(-D)` *is* the ideal sheaf `ℐ_D` of the
closed subscheme `D ⊆ S`. -/
@[stacks 01WX "(3): O_S(-D) = I_D"]
noncomputable abbrev negativeTwist : SheafOfModules.{u} (structureSheafRing X.toRingedSpace) :=
  Stacks.ClosedImmersion.idealSheaf D.subschemeι.toLRSHom.toShHom

/-- The inclusion `ℐ_D ⟶ 𝒪_S` of the ideal sheaf of a closed subscheme into the structure
sheaf: the kernel inclusion of the surjection `𝒪_S ⟶ i_* 𝒪_D` that defines `ℐ_D`. -/
noncomputable abbrev idealInclusion :
    negativeTwist D ⟶ SheafOfModules.unit (structureSheafRing X.toRingedSpace) :=
  kernel.ι (SheafOfModules.unitToPushforwardObjUnit
    (structureSheafHom D.subschemeι.toLRSHom.toShHom))

/-- **Stacks Project, Tag 01WX (1).** The sheaf `𝒪_S(D) = SheafHom_{𝒪_S}(ℐ_D, 𝒪_S)` associated
to a closed subscheme `D ⊆ S`: the dual of its ideal sheaf. -/
@[stacks 01WX "(1): O_S(D) = SheafHom(I_D, O_S)"]
noncomputable abbrev invertibleSheaf : SheafOfModules.{u} (structureSheafRing X.toRingedSpace) :=
  Stacks.SheafOfModules.dualSheaf X.sheaf.obj (structureSheafRing X.toRingedSpace).property
    (negativeTwist D)

/-- **Stacks Project, Tag 01WX (4).** The difference twist
`𝒪_S(D - D') = 𝒪_S(D) ⊗_{𝒪_S} 𝒪_S(-D')`. The expression `D - D'` has no geometric meaning on
its own; this is the definition of the sheaf it names. -/
@[stacks 01WX "(4): O_S(D - D') = O_S(D) tensor O_S(-D')"]
noncomputable abbrev differenceTwist : SheafOfModules.{u} (structureSheafRing X.toRingedSpace) :=
  (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.sheaf.obj,
      Presheaf.isSheaf_of_isSheaf_comp _ (X.sheaf.obj) (forget₂ CommRingCat RingCat)
        ((structureSheafRing X.toRingedSpace).property)⟩).obj ((invertibleSheaf D))).obj
    ((negativeTwist D')))

section EffectiveCartier

variable [hD : IsEffectiveCartierDivisor D]

/-- The ideal sheaf of an effective Cartier divisor is invertible in the spelling the
evaluation pairing is stated for. `IsEffectiveCartierDivisor` is stated with
`AlgebraicGeometry.SheafOfModules.IsInvertible` and with the structure sheaf written
`X.sheaf.obj` over `structureSheafRing`; the pairing wants
`Stacks.SheafOfModules.IsInvertible` with `X.presheaf` over `structureSheafRing`. Each pair is
equal by `rfl`, but instance search is syntactic, so the crossing is made once here. -/
theorem stacksIsInvertible_negativeTwist :
    Stacks.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X.toRingedSpace).property (negativeTwist D) :=
  have _ : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf
    (structureSheafRing X.toRingedSpace).property (negativeTwist D) := hD
  Stacks.InvertibleBridge.stacksIsInvertible_of_algebraicGeometryIsInvertible

/-- **The evaluation pairing `𝒪_S(D) ⊗_{𝒪_S} ℐ_D ≅ 𝒪_S`.** This is what identifies `𝒪_S(D)` as
*the* tensor inverse of `ℐ_D`, and it is the normalization of the two identifications below. -/
noncomputable def invertibleSheafPairing :
    (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.sheaf.obj,
        Presheaf.isSheaf_of_isSheaf_comp _ (X.sheaf.obj) (forget₂ CommRingCat RingCat)
          ((structureSheafRing X.toRingedSpace).property)⟩).obj ((invertibleSheaf D))).obj
      ((negativeTwist D))) ≅
      SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf X.sheaf.obj
        (structureSheafRing X.toRingedSpace).property) :=
  have := stacksIsInvertible_negativeTwist D
  Stacks.SheafOfModules.Scheme.evaluationIso X (negativeTwist D)

/-- **The evaluation pairing `ℐ_D ⊗_{𝒪_S} 𝒪_S(D) ≅ 𝒪_S`**, the other factor order. -/
noncomputable def invertibleSheafPairing' :
    (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.sheaf.obj,
        Presheaf.isSheaf_of_isSheaf_comp _ (X.sheaf.obj) (forget₂ CommRingCat RingCat)
          ((structureSheafRing X.toRingedSpace).property)⟩).obj ((negativeTwist D))).obj
      ((invertibleSheaf D))) ≅
      SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf X.sheaf.obj
        (structureSheafRing X.toRingedSpace).property) :=
  Stacks.SheafOfModules.tensorSheafBraiding X.sheaf.obj
    (structureSheafRing X.toRingedSpace).property (negativeTwist D) (invertibleSheaf D) ≪≫
      invertibleSheafPairing D

/-- **Stacks Project, Tag 01WX (1).** The sheaf `𝒪_S(D)` of an effective Cartier divisor is
invertible, which is what the tag's wording "the invertible sheaf `𝒪_S(D)`" asserts.

This is Tag 0B8K (2) ⟹ (1) applied to the evaluation pairing: no trivializing cover is
constructed, and no rank-one dual basis is assumed. -/
@[stacks 01WX "(1): O_S(D) is invertible"]
instance isInvertible_invertibleSheaf :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj
      (structureSheafRing X.toRingedSpace).property (invertibleSheaf D) :=
  have : Stacks.SheafOfModules.IsInvertible X.sheaf.obj
      (structureSheafRing X.toRingedSpace).property (invertibleSheaf D) :=
    Stacks.SheafOfModules.isInvertible_of_tensorIsoUnit X.sheaf.obj
      (structureSheafRing X.toRingedSpace).property (invertibleSheaf D) (negativeTwist D)
      (invertibleSheafPairing' D)
  Stacks.InvertibleBridge.algebraicGeometryIsInvertible_of_stacksIsInvertible

/-- **Stacks Project, Tag 01WX (1):** `𝒪_S(D) = ℐ_D^{⊗ -1}`. The dual of the ideal sheaf is its
negative first tensor power, by uniqueness of tensor inverses; the identification is the one
normalized by `invertibleSheafPairing`, not an arbitrary isomorphism. That normalization needs
no restatement here: this *is*
`Stacks.SheafOfModules.Invertible.isoTensorPowerNegOne` at that pairing, so
`Stacks.SheafOfModules.Invertible.isoTensorPowerNegOne_hom_tensor` applies to it directly and
says that tensoring this isomorphism with `ℐ_D` carries the canonical trivialization of
`ℐ_D^{⊗ -1} ⊗ ℐ_D` back to `invertibleSheafPairing`. -/
@[stacks 01WX "(1): O_S(D) = I_D^{tensor -1}"]
noncomputable def invertibleSheafIsoNegativeTensorPower :
    invertibleSheaf D ≅ Stacks.SheafOfModules.Invertible.tensorPower X.sheaf.obj
      (structureSheafRing X.toRingedSpace).property (negativeTwist D) (-1) :=
  Stacks.SheafOfModules.Invertible.isoTensorPowerNegOne X.sheaf.obj
    (structureSheafRing X.toRingedSpace).property (negativeTwist D) (invertibleSheaf D)
    (invertibleSheafPairing D)

/-- **Stacks Project, Tag 01WX (3):** `𝒪_S(-D) = 𝒪_S(D)^{⊗ -1}`. Together with the definition
of `negativeTwist` this is the tag's full chain `𝒪_S(-D) = 𝒪_S(D)^{⊗ -1} = ℐ_D`. The
identification is normalized by `invertibleSheafPairing'`, through the same
`Stacks.SheafOfModules.Invertible.isoTensorPowerNegOne_hom_tensor`. -/
@[stacks 01WX "(3): O_S(-D) = O_S(D)^{tensor -1}"]
noncomputable def negativeTwistIsoNegativeTensorPower :
    negativeTwist D ≅ Stacks.SheafOfModules.Invertible.tensorPower X.sheaf.obj
      (structureSheafRing X.toRingedSpace).property (invertibleSheaf D) (-1) :=
  Stacks.SheafOfModules.Invertible.isoTensorPowerNegOne X.sheaf.obj
    (structureSheafRing X.toRingedSpace).property (invertibleSheaf D) (negativeTwist D)
    (invertibleSheafPairing' D)

end EffectiveCartier

/-- **Stacks Project, Tag 01WX (2).** The canonical section `1 = 1_D`: the global section of
`𝒪_S(D)` corresponding to the inclusion mapping `ℐ_D ⟶ 𝒪_S`.

A section of `SheafHom(ℐ_D, 𝒪_S)` over an open `U` is a morphism `ℐ_D|_U ⟶ 𝒪_S|_U` of
presheaves of modules on the slice site over `U` (Tag 03EM), so the global section in question
is the restriction of `idealInclusion` to the slice site over `⊤`. -/
@[stacks 01WX "(2): the canonical section"]
noncomputable def canonicalSection : (invertibleSheaf D).val.obj (op (⊤ : Opens X)) :=
  (restrFun X.sheaf.obj ⊤).map (idealInclusion D).val

/-- **The canonical section is the one corresponding to the ideal inclusion**: evaluated on a
section of `ℐ_D` over the whole of `S`, it returns that section's image under
`idealInclusion`. -/
@[simp]
theorem evalSection_canonicalSection (x : (negativeTwist D).val.obj (op (⊤ : Opens X))) :
    Stacks.SheafOfModules.evalSection X.sheaf.obj (negativeTwist D).val
        (SheafOfModules.unit (structureSheafRing X.toRingedSpace)).val (op ⊤)
        (canonicalSection D) x =
      ((idealInclusion D).val.app (op ⊤)).hom x := rfl

end Stacks.Divisors

end
