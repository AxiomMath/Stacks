module

public import StacksFrontier.AlgebraicGeometry.Spaces.RingedSite
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRingedToposHom
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.Points
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SquareZeroExtensionShortExact
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.StructureSheafSquareZeroExtension
public import StacksFrontier.Topology.Dimension.KrullSupplement

/-!
# Elementary consequences of the data of a square-zero extension of `𝒪_X`

Let `f : X ⟶ Y` be a morphism of algebraic spaces and `E` a square-zero extension of the structure
sheaf of `X` relative to `f`, in the sense of `AlgebraicGeometry.Space.SquareZeroExtension` (the
data of Stacks 05ZT): a short exact sequence `0 ⟶ ℐ ⟶ 𝒜 ⟶ 𝒪_X ⟶ 0` of sheaves on the small
étale site of `X` with `𝒜` an `f⁻¹𝒪_Y`-algebra and `ℐ` a quasi-coherent ideal of square zero.
This file reads the fields of that structure on sections over a single étale chart.

## Main results

* `AlgebraicGeometry.Space.SquareZeroExtension.ι_eq_zero_iff` — a section of the kernel vanishes
  exactly when its image in `𝒜` does (injectivity of the inclusion is
  `AlgebraicGeometry.Space.SquareZeroExtension.injective_ι`).
* `AlgebraicGeometry.Space.SquareZeroExtension.exists_ι_eq` — over every étale chart, a section
  of `𝒜` killed by `π` comes from `ℐ`: the sequence is exact on sections, not merely locally.
* `AlgebraicGeometry.Space.SquareZeroExtension.mul_eq_zero_of_mem_ker` — the kernel is an ideal
  of square zero, read on sections.
* `AlgebraicGeometry.Space.SquareZeroExtension.comp_app_apply` — the algebra structure is
  compatible with the structure map of `f`, read on sections.

## References

* [Stacks Project, Tag 05ZT](https://stacks.math.columbia.edu/tag/05ZT)
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace SquareZeroExtension

variable {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y} (E : SquareZeroExtension B S hS f)

/-- A section of the kernel vanishes exactly when its image in `𝒜` does. -/
theorem ι_eq_zero_iff (U : (SmallEtale B S hS X.1)ᵒᵖ) (x : E.I.val.obj U) :
    E.ι U x = 0 ↔ x = 0 :=
  ⟨fun h => injective_ι B S hS E U (by simpa using h), fun h => by simp [h]⟩

/-- **The sequence is exact on sections over every étale chart**, not merely locally: a section
of `𝒜` killed by `π` is the image of a section of `ℐ`. This is the existence half of
`exact_kernel`, stated without the uniqueness. -/
theorem exists_ι_eq (U : (SmallEtale B S hS X.1)ᵒᵖ) (a : E.A.obj.obj U)
    (ha : E.π.hom.app U a = 0) : ∃ x, E.ι U x = a :=
  let ⟨x, hx, _⟩ := E.exact_kernel U a ha
  ⟨x, hx⟩

/-- **The kernel is an ideal of square zero, read on sections.** Two sections of `𝒜` over an
étale chart that are killed by `π` have zero product. -/
theorem mul_eq_zero_of_mem_ker (U : (SmallEtale B S hS X.1)ᵒᵖ) (a b : E.A.obj.obj U)
    (ha : E.π.hom.app U a = 0) (hb : E.π.hom.app U b = 0) : a * b = 0 := by
  obtain ⟨x, hx⟩ := E.exists_ι_eq U a ha
  obtain ⟨y, hy⟩ := E.exists_ι_eq U b hb
  rw [← hx, ← hy]
  exact E.square_zero U x y

/-- **The kernel absorbs multiplication by any section.** The product of a section of `𝒜` with a
section of the kernel is again in the kernel: it is the image of the `𝒪_X`-action on `ℐ`. -/
theorem mul_mem_ker (U : (SmallEtale B S hS X.1)ᵒᵖ) (a : E.A.obj.obj U)
    (x : E.I.val.obj U) : ∃ y, E.ι U y = a * E.ι U x :=
  ⟨((E.I.val.obj U).smul (E.π.hom.app U a)).hom x, E.smul_lift U a x⟩

/-- **The algebra structure is compatible with the structure map of `f`, on sections.** This is
`toBase_π` evaluated at an étale chart, with the composite left as a composite. -/
theorem comp_app_apply (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (a : ((inverseImageCommRingFunctor (smallEtaleRingedToposHom B S hS f).toToposHom).obj
      (smallEtaleRingedTopos B S hS Y).O).obj.obj U) :
    (E.toBase ≫ E.π).hom.app U a =
      (smallEtaleRingedToposHom B S hS f).fSharpInverseImage.hom.app U a :=
  ConcreteCategory.congr_hom
    (congrArg
      (fun φ : (inverseImageCommRingFunctor (smallEtaleRingedToposHom B S hS f).toToposHom).obj
            (smallEtaleRingedTopos B S hS Y).O ⟶ (smallEtaleRingedTopos B S hS X).O =>
        φ.hom.app U)
      E.toBase_π) a

end SquareZeroExtension

end AlgebraicGeometry.Space

end
