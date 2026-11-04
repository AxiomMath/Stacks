module

public import StacksFrontier.AlgebraicGeometry.DeRham.LogPoles.FormsSheaf

/-!
# The ideal sheaf acts into the forms vanishing on the divisor

Let `f : X ⟶ S` be a morphism of schemes and let `I` cut out a closed subscheme `Y ⊆ X` with
ideal sheaf `ℐ`. A relative `p`-form multiplied by a local section of `ℐ` restricts to zero on
`Y`: the restriction map is `𝒪_X`-linear, and a section of `ℐ` acts as zero on the sections of
any direct image from `Y`, because that action is through `𝒪_X ⟶ i_*𝒪_Y` and `ℐ` is by
definition the kernel of that map.

This is the multiplication `ℐ · Ω^p_{X/S} ⊆ 𝒦^p` underlying the canonical inclusion
`Ω^p_{X/S} ⟶ Ω^p_{X/S}(log Y)` of
[Stacks, Tag 0FMW], which sends a form with no pole to the map `a ↦ a · ω` of
`AlgebraicGeometry.Scheme.Hom.logPolesForms`.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.negativeTwistSection`: the structure-sheaf section underlying a
  local section of the ideal sheaf.

## Main results

* `AlgebraicGeometry.Scheme.Hom.negativeTwistSection_smul_pushforward_eq_zero`: a local section
  of the ideal sheaf annihilates the sections of a direct image from the closed subscheme.
* `AlgebraicGeometry.Scheme.Hom.negativeTwistSection_smul_mem_formRestrictionKernel`: a relative
  form multiplied by a local section of the ideal sheaf lies in `𝒦^p`.

## Implementation notes

`Stacks.Divisors.negativeTwist I` is the ideal sheaf as an abstract kernel in sheaves of
`𝒪_X`-modules, so a local section of it is not literally a section of `𝒪_X`; it is carried to
one by `Stacks.Divisors.idealInclusion`, which is the kernel inclusion. That is what
`negativeTwistSection` names, with its value ascribed to the `RingCat` spelling
`X.ringCatSheaf.obj.obj (op V)` rather than to `Γ(X, V)`: the module structures on the sections
of a sheaf of `𝒪_X`-modules are declared over the former, and instance search does not cross
between the two even though they are definitionally equal.

The scalar action on the sections of a direct image is the action through the structure-sheaf map,
and the kernel condition of `Stacks.Divisors.idealInclusion` is exactly that a section of the
ideal sheaf is carried to zero by that map; both steps are definitional.

## References

* [Stacks Project, Tag 0FMW](https://stacks.math.columbia.edu/tag/0FMW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S) (I : X.IdealSheafData)

/-- The section of `𝒪_X` underlying a local section of the ideal sheaf of `I`, through the
kernel inclusion `ℐ ⟶ 𝒪_X`. -/
def negativeTwistSection (V : X.Opens)
    (a : (Stacks.Divisors.negativeTwist I).val.obj (op V)) :
    X.ringCatSheaf.obj.obj (op V) :=
  PresheafOfModules.Hom.app (Stacks.Divisors.idealInclusion I).val (op V) a

/-- A local section of the ideal sheaf of `I` is carried to zero by `𝒪_X ⟶ i_*𝒪_Y`: that is
the kernel condition defining the ideal sheaf. -/
theorem structureSheafHom_negativeTwistSection (V : X.Opens)
    (a : (Stacks.Divisors.negativeTwist I).val.obj (op V)) :
    (RingedSpaceModuleAdjunction.structureSheafHom
        I.subschemeι.toLRSHom.toShHom).hom.app (op V) (negativeTwistSection I V a) = 0 :=
  congrArg (fun φ => PresheafOfModules.Hom.app (_root_.SheafOfModules.Hom.val φ) (op V) a)
    (kernel.condition (_root_.SheafOfModules.unitToPushforwardObjUnit
      (RingedSpaceModuleAdjunction.structureSheafHom I.subschemeι.toLRSHom.toShHom)))

/-- **A local section of the ideal sheaf annihilates the sections of a direct image from the
closed subscheme.** The scalar action on the sections of `i_*F` over `V` is the action of
`𝒪_Y(i⁻¹V)` through `𝒪_X(V) ⟶ 𝒪_Y(i⁻¹V)`, and a section of the ideal sheaf goes to zero. -/
theorem negativeTwistSection_smul_pushforward_eq_zero (F : I.subscheme.Modules) (V : X.Opens)
    (a : (Stacks.Divisors.negativeTwist I).val.obj (op V))
    (z : ((Scheme.Modules.pushforward I.subschemeι).obj F).val.obj (op V)) :
    negativeTwistSection I V a • z = 0 := by
  refine Eq.trans ?_ (zero_smul (I.subscheme.ringCatSheaf.obj.obj (op (I.subschemeι ⁻¹ᵁ V)))
    (show F.val.obj (op (I.subschemeι ⁻¹ᵁ V)) from z))
  exact congrArg (fun c : I.subscheme.ringCatSheaf.obj.obj (op (I.subschemeι ⁻¹ᵁ V)) =>
      c • (show F.val.obj (op (I.subschemeι ⁻¹ᵁ V)) from z))
    (structureSheafHom_negativeTwistSection I V a)

/-- **A relative form multiplied by a local section of the ideal sheaf restricts to zero on the
divisor**, so it lies in the subsheaf `𝒦^p`. -/
theorem negativeTwistSection_smul_mem_formRestrictionKernel (p : ℕ) (V : X.Opens)
    (a : (Stacks.Divisors.negativeTwist I).val.obj (op V))
    (ω : (relativeDifferentialForms f (p : ℤ)).val.obj (op V)) :
    negativeTwistSection I V a • ω ∈ (formRestrictionKernel f I p).obj (op V) := by
  rw [mem_formRestrictionKernel,
    show PresheafOfModules.Hom.app (formRestriction I.subschemeι f (p : ℤ)).val (op V)
          (negativeTwistSection I V a • ω) =
        negativeTwistSection I V a •
          PresheafOfModules.Hom.app (formRestriction I.subschemeι f (p : ℤ)).val (op V) ω from
      map_smul _ _ _]
  exact negativeTwistSection_smul_pushforward_eq_zero I _ V a _

end AlgebraicGeometry.Scheme.Hom

end
