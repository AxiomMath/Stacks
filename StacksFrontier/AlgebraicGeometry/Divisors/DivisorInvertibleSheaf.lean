module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleCompare
public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.Defs
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier
public import StacksFrontier.AlgebraicGeometry.Divisors.TensorPower
public import StacksFrontier.AlgebraicGeometry.InvertibleDual.Evaluation
public import StacksFrontier.AlgebraicGeometry.Thickenings.ConormalSheaf

/-!
# The invertible sheaf of an effective Cartier divisor

Let `X` be a scheme and let `D ⊆ X` be an effective Cartier divisor, i.e. a closed subscheme
whose sheaf of ideals `ℐ_D ⊆ 𝒪_X` is an invertible `𝒪_X`-module. The *invertible sheaf
associated to `D`* is the dual

`𝒪_X(D) = SheafHom_{𝒪_X}(ℐ_D, 𝒪_X)`,

and the inclusion `ℐ_D ⟶ 𝒪_X` is itself a global section of it, the *canonical section* `1_D`.
Dually one writes `𝒪_X(-D) = ℐ_D`, and for a second effective Cartier divisor `D'`,
`𝒪_X(D - D') = 𝒪_X(D) ⊗_{𝒪_X} 𝒪_X(-D')`.

## Main definitions

* `Stacks.Divisors.invertibleSheaf'`: the sheaf `𝒪_X(D)`.
* `Stacks.Divisors.canonicalSection'`: the canonical global section `1_D` of `𝒪_X(D)`, as a
  compatible family of sections over every open.
* `Stacks.Divisors.negativeTwist'`: the sheaf `𝒪_X(-D)`, which is `ℐ_D`.
* `Stacks.Divisors.differenceTwist'`: the sheaf `𝒪_X(D - D')`.

The four names are primed because `StacksFrontier.AlgebraicGeometry.Divisors.InvertibleSheaf`
carries the same four objects unprimed. The three sheaves are the same sheaves; what differs is
the spelling of the sheaf of rings indexing them,
`structureSheafRing` here against
`AlgebraicGeometry.structureSheafRing` there. The two are equal by `rfl`, but
instance search is syntactic, so each spelling carries its own invertibility instances and its
own downstream API, and the two cannot be collapsed. The canonical sections differ further:
this one is a compatible family of sections over every open, the unprimed one a single section
over `⊤`.

## Main results

* `Stacks.Divisors.invertibleSheaf_isInvertible`: `𝒪_X(D)` is invertible.
* `Stacks.Divisors.invertibleSheafIsoInverseIdeal`: `𝒪_X(D)` is the inverse tensor power
  `ℐ_D^{⊗ -1}`, so `𝒪_X(D)` really is the tensor inverse of the ideal sheaf and not merely a
  dual.
* `Stacks.Divisors.negativeTwistIso`: dually, `ℐ_D` is the inverse tensor power
  `𝒪_X(D)^{⊗ -1}`.
* `Stacks.Divisors.canonicalSection_val`: the component of `1_D` over an open `U` is the
  restriction of the ideal inclusion to `U`.
* `Stacks.Divisors.isTensorInvertible_negativeTwist` and
  `Stacks.Divisors.isTensorInvertible_invertibleSheaf`: the same two invertibility statements in
  the second of the library's two spellings of invertibility of a sheaf of modules.

## Implementation notes

A closed subscheme of `X` is represented by `AlgebraicGeometry.Scheme.IdealSheafData`, and its
sheaf of ideals as a sheaf of modules is `Stacks.ClosedImmersion.idealSheaf` of the associated
closed immersion `D.subschemeι`; this is the spelling in which
`Stacks.Divisors.IsEffectiveCartierDivisor` is stated. The dual is
`Stacks.SheafOfModules.dualSheaf`, whose sections over `U` are *by definition* the
`𝒪_X|_U`-linear maps `ℐ_D|_U ⟶ 𝒪_X|_U` on the slice site over `U`. Consequently the canonical
section needs no identification of the sections of a sheaf-hom with a hom-set: its component
over `U` is literally the restriction of the inclusion `ℐ_D ⟶ 𝒪_X` to the slice site, and
compatibility with the restriction maps of the sheaf-hom holds by definition.

Invertibility of `𝒪_X(D)` is read off from the evaluation pairing
`Stacks.SheafOfModules.Scheme.evaluationIso`, which identifies `ℐ_D^∨ ⊗ ℐ_D` with `𝒪_X`: a
sheaf admitting a trivializing pairing is invertible. The same two pairings, fed to
`Stacks.SheafOfModules.isoOfTensorIsoUnit` (uniqueness of tensor inverses), identify the dual
with the `(-1)`st tensor power in both directions.

Two spellings of invertibility of a sheaf of modules occur in this library;
`Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry` identifies them, and
`Stacks.Divisors.negativeTwist_isInvertible` below is that identification at the ideal sheaf of
an effective Cartier divisor, registered so that the tensor-power API — which is stated for the
`Stacks` spelling — applies to a divisor with no manual transport.

## References

* [Stacks Project, Tag 01WX](https://stacks.math.columbia.edu/tag/01WX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Stacks.SheafOfModules.TensorSheafification
open Stacks.SheafOfModules (dualSheaf)

universe u

namespace Stacks.Divisors

variable {X : Scheme.{u}} (D D' : X.IdealSheafData)

/-- **Stacks Project, Tag 01WX (3).** The sheaf `𝒪_X(-D) = ℐ_D` of a closed subscheme
`D ⊆ X`: its sheaf of ideals. -/
@[stacks 01WX "part (3): negative twist"]
noncomputable abbrev negativeTwist' : SheafOfModules.{u} (structureSheafRing X.toRingedSpace) :=
  Stacks.ClosedImmersion.idealSheaf D.subschemeι.toLRSHom.toShHom

/-- **Stacks Project, Tag 01WX (1).** The sheaf `𝒪_X(D) = SheafHom_{𝒪_X}(ℐ_D, 𝒪_X)` associated
to a closed subscheme `D ⊆ X`. It is invertible as soon as `D` is an effective Cartier divisor;
see `Stacks.Divisors.invertibleSheaf_isInvertible`. -/
@[stacks 01WX "part (1): associated sheaf"]
noncomputable abbrev invertibleSheaf' : SheafOfModules.{u} (structureSheafRing X.toRingedSpace) :=
  dualSheaf X.presheaf (structureSheafRing X.toRingedSpace).property (negativeTwist' D)

/-- The sheaf of ideals of an effective Cartier divisor is invertible, stated at the index
`(X.presheaf, (structureSheafRing X.toRingedSpace).property)` rather than the one
`Stacks.Divisors.IsEffectiveCartierDivisor` is written with. The two indices are the same, so
this is a re-spelling; it is registered as an instance because the tensor-power API of
[Stacks, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU) resolves its hypothesis by
instance search at this spelling. -/
instance isInvertible_negativeTwist [h : IsEffectiveCartierDivisor D] :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X.toRingedSpace).property (negativeTwist' D) := h

/-- The sheaf of ideals of an effective Cartier divisor is invertible in the sense of
`Stacks.SheafOfModules.IsInvertible`. The two formalisations of invertibility agree by
`Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry`; this is that identification at the
ideal sheaf of a divisor, and it is what the evaluation pairing consumes. -/
theorem isTensorInvertible_negativeTwist [IsEffectiveCartierDivisor D] :
    Stacks.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X.toRingedSpace).property (negativeTwist' D) :=
  (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mpr
    (isInvertible_negativeTwist D)

/-- The sheaf `𝒪_X(D)` of an effective Cartier divisor is invertible in the sense of
`Stacks.SheafOfModules.IsInvertible`: the evaluation pairing trivializes it. -/
private theorem isTensorInvertible_invertibleSheaf_aux [IsEffectiveCartierDivisor D] :
    Stacks.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X.toRingedSpace).property (invertibleSheaf' D) :=
  have := isTensorInvertible_negativeTwist D
  Stacks.SheafOfModules.isInvertible_of_tensorIsoUnit _ _ _ (negativeTwist' D)
    (Stacks.SheafOfModules.tensorSheafBraiding _ _ _ _ ≪≫
      Stacks.SheafOfModules.Scheme.evaluationIso X (negativeTwist' D))

/-- **Stacks Project, Tag 01WX (1).** The sheaf `𝒪_X(D)` of an effective Cartier divisor is
invertible: the evaluation pairing `𝒪_X(D) ⊗ ℐ_D ⟶ 𝒪_X` trivializes it. -/
@[stacks 01WX "part (1): invertibility", instance]
theorem invertibleSheaf_isInvertible [IsEffectiveCartierDivisor D] :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X.toRingedSpace).property (invertibleSheaf' D) :=
  Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _
    (isTensorInvertible_invertibleSheaf_aux D)

/-- The sheaf `𝒪_X(D)` of an effective Cartier divisor is invertible in the sense of
`Stacks.SheafOfModules.IsInvertible`; see `Stacks.Divisors.invertibleSheaf_isInvertible`. -/
theorem isTensorInvertible_invertibleSheaf [IsEffectiveCartierDivisor D] :
    Stacks.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X.toRingedSpace).property (invertibleSheaf' D) :=
  isTensorInvertible_invertibleSheaf_aux D

/-- The component over an open `U` of the canonical section of `𝒪_X(D)`: the restriction to the
slice site over `U` of the inclusion `ℐ_D ⟶ 𝒪_X`. The sections of `𝒪_X(D)` over `U` are by
definition the `𝒪_X|_U`-linear maps `ℐ_D|_U ⟶ 𝒪_X|_U`, so this is exactly the ideal inclusion
read over `U`. -/
noncomputable def canonicalSectionComponent (U : Opens X) :
    (invertibleSheaf' D).val.obj (op U) :=
  (restrFun X.presheaf U).map
    (Stacks.ClosedImmersion.idealSheafι D.subschemeι.toLRSHom.toShHom).val

/-- **Stacks Project, Tag 01WX (2).** The canonical section `1_D` of `𝒪_X(D)`: the global
section corresponding to the inclusion of the ideal sheaf `ℐ_D` into `𝒪_X`. -/
@[stacks 01WX "part (2): canonical section"]
noncomputable def canonicalSection' : (invertibleSheaf' D).sections :=
  (invertibleSheaf' D).val.sectionsMk (fun U => canonicalSectionComponent D U.unop)
    (fun _ _ _ => rfl)

/-- The canonical section of `𝒪_X(D)` is, over every open `U`, the restricted ideal
inclusion. -/
@[simp]
theorem canonicalSection_val (U : Opens X) :
    (canonicalSection' D).val (op U) = canonicalSectionComponent D U := rfl

/-- **Stacks Project, Tag 01WX (1).** The sheaf `𝒪_X(D)` of an effective Cartier divisor is the
inverse tensor power `ℐ_D^{⊗ -1}` of its ideal sheaf: both are tensor inverses of `ℐ_D`, and a
tensor inverse is unique up to a canonical isomorphism. -/
@[stacks 01WX "part (1): inverse tensor power"]
noncomputable def invertibleSheafIsoInverseIdeal [IsEffectiveCartierDivisor D] :
    Stacks.SheafOfModules.Invertible.tensorPower X.presheaf
        (structureSheafRing X.toRingedSpace).property (negativeTwist' D) (-1) ≅
      invertibleSheaf' D :=
  haveI := isTensorInvertible_negativeTwist D
  Stacks.SheafOfModules.isoOfTensorIsoUnit _ _ (negativeTwist' D) _ _
    (Stacks.SheafOfModules.Invertible.tensorPowerSuccIso _ _ (negativeTwist' D) (-1) ≪≫
      Stacks.SheafOfModules.Invertible.tensorPowerReindex _ _ (negativeTwist' D)
        (neg_add_cancel 1) ≪≫
      eqToIso (Stacks.SheafOfModules.Invertible.tensorPower_zero _ _ _))
    (Stacks.SheafOfModules.Scheme.evaluationIso X (negativeTwist' D))

/-- **Stacks Project, Tag 01WX (3).** The sheaf `𝒪_X(-D) = ℐ_D` is the inverse tensor power
`𝒪_X(D)^{⊗ -1}`, which is the sense in which `𝒪_X(-D)` is the inverse of `𝒪_X(D)`. -/
@[stacks 01WX "part (3): inverse tensor power"]
noncomputable def negativeTwistIso [IsEffectiveCartierDivisor D] :
    Stacks.SheafOfModules.Invertible.tensorPower X.presheaf
        (structureSheafRing X.toRingedSpace).property (invertibleSheaf' D) (-1) ≅
      negativeTwist' D :=
  haveI := isTensorInvertible_negativeTwist D
  haveI := isTensorInvertible_invertibleSheaf D
  Stacks.SheafOfModules.isoOfTensorIsoUnit _ _ (invertibleSheaf' D) _ _
    (Stacks.SheafOfModules.Invertible.tensorPowerSuccIso _ _ (invertibleSheaf' D) (-1) ≪≫
      Stacks.SheafOfModules.Invertible.tensorPowerReindex _ _ (invertibleSheaf' D)
        (neg_add_cancel 1) ≪≫
      eqToIso (Stacks.SheafOfModules.Invertible.tensorPower_zero _ _ _))
    (Stacks.SheafOfModules.tensorSheafBraiding _ _ _ _ ≪≫
      Stacks.SheafOfModules.Scheme.evaluationIso X (negativeTwist' D))

/-- **Stacks Project, Tag 01WX (4).** The sheaf
`𝒪_X(D - D') = 𝒪_X(D) ⊗_{𝒪_X} 𝒪_X(-D')` attached to a pair of closed subschemes. -/
@[stacks 01WX "part (4): difference twist"]
noncomputable abbrev differenceTwist' : SheafOfModules.{u} (structureSheafRing X.toRingedSpace) :=
  (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ (X.presheaf) (forget₂ CommRingCat RingCat)
        ((structureSheafRing X.toRingedSpace).property)⟩).obj
      ((invertibleSheaf' D))).obj ((negativeTwist' D')))

end Stacks.Divisors

end
