module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.IdealPowerQuotient
public import StacksFrontier.AlgebraicGeometry.Modules.IdealPowerMultiple

/-!
# The tower of ideal-power quotients of a sheaf of modules

Let `X` be a scheme, `I` a quasi-coherent ideal sheaf on `X` and `F` a sheaf of modules. The
subsheaves `I ^ n F` decrease as `n` grows, so the quotients `F / I ^ n F` form an inverse system
indexed by `ℕᵒᵖ`, and the cokernel projections `F ⟶ F / I ^ n F` assemble into a cone over it with
vertex `F`. The limit of this inverse system is the `I`-adic completion of `F`.

## Main definitions

* `Stacks.Algebraization.quotientMapOfLE` — the map `M / N ⟶ M / N'` induced by `N ≤ N'`.
* `Stacks.Algebraization.adicQuotientSystem` — the inverse system `n ↦ F / I ^ n F`.
* `Stacks.Algebraization.adicQuotientCone` — the cone over it with vertex `F`.

## Main results

* `Stacks.Algebraization.idealPowerMultiple_antitone` — `I ^ m F ≤ I ^ n F` for `n ≤ m`.
* `Stacks.Algebraization.quotientMapOfLE_π` — the induced map commutes with the projections.

## Implementation notes

`quotientMapOfLE` is phrased for an arbitrary pair of submodules rather than only for ideal
powers.

`AlgebraicGeometry.Scheme.Modules` is a `def` for `SheafOfModules X.ringCatSheaf`, so instance
resolution does not find Mathlib's `CompleteLattice M.Submodule` at that shape; the lattice is
supplied by the local instance below. The two categories are definitionally equal but carry
separately declared category instances, and a composite mixing the two is not type-correct at the
transparency `rw` uses to build its motive; `submoduleInclusion` restates
`SheafOfModules.Submodule.homOfLE` at `X.Modules` so that every composite stays inside a single
instance.

## References

* [Stacks Project, Tag 0880](https://stacks.math.columbia.edu/tag/0880)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Algebraization

/-- Higher ideal powers cut out smaller subsheaves: `I ^ m F ≤ I ^ n F` whenever `n ≤ m`. -/
public theorem idealPowerMultiple_antitone {X : Scheme.{u}} (I : X.IdealSheafData)
    (F : X.Modules) {n m : ℕ} (h : n ≤ m) :
    idealPowerMultiple I m F ≤ idealPowerMultiple I n F :=
  (idealPowerMultiple_le_iff I m F _).2 fun U ↦
    (Submodule.smul_mono_left (Ideal.pow_le_pow_right h)).trans
      ((idealPowerMultiple_le_iff I n F _).1 le_rfl U)

/-- `SheafOfModules.Submodule.homOfLE`, at the `X.Modules` presentation of the category of
sheaves of modules on `X`. -/
public def submoduleInclusion {X : Scheme.{u}} {F : X.Modules} {N M : F.Submodule} (h : N ≤ M) :
    (N.toSheafOfModules : X.Modules) ⟶ (M.toSheafOfModules : X.Modules) :=
  SheafOfModules.Submodule.homOfLE h

/-- The inclusion `N ⟶ M` followed by the inclusion of `M` into the ambient sheaf is the
inclusion of `N`. -/
public lemma submoduleInclusion_comp_ι {X : Scheme.{u}} {F : X.Modules} {N M : F.Submodule}
    (h : N ≤ M) :
    submoduleInclusion h ≫ (M.ι : (M.toSheafOfModules : X.Modules) ⟶ F) = N.ι :=
  SheafOfModules.Submodule.homOfLE_ι h

/-- The map on sheaf quotients induced by an inclusion of submodules. -/
public def quotientMapOfLE {X : Scheme.{u}} {F : X.Modules}
    {N M : F.Submodule} (h : N ≤ M) :
    cokernel (C := X.Modules) N.ι ⟶ cokernel (C := X.Modules) M.ι :=
  cokernel.desc (C := X.Modules) N.ι (cokernel.π (C := X.Modules) M.ι)
    (((congrArg (fun g => g ≫ cokernel.π (C := X.Modules) M.ι)
          (submoduleInclusion_comp_ι h).symm).trans
        (Category.assoc _ _ _)).trans
      ((congrArg (fun g => submoduleInclusion h ≫ g)
          (cokernel.condition (C := X.Modules) M.ι)).trans comp_zero))

/-- The induced map on quotients commutes with the quotient projections. -/
public theorem quotientMapOfLE_π {X : Scheme.{u}} {F : X.Modules}
    {N M : F.Submodule} (h : N ≤ M) :
    cokernel.π (C := X.Modules) N.ι ≫ quotientMapOfLE h =
      cokernel.π (C := X.Modules) M.ι :=
  cokernel.π_desc _ _ _

/-- The canonical tower of quotients by the powers of an ideal sheaf. -/
public def adicQuotientSystem {X : Scheme.{u}} (I : X.IdealSheafData) (F : X.Modules) :
    ℕᵒᵖ ⥤ X.Modules where
  obj n := cokernel (C := X.Modules) (idealPowerMultiple I n.unop F).ι
  map h := quotientMapOfLE (idealPowerMultiple_antitone I F (leOfHom h.unop))
  map_id n := by
    refine coequalizer.hom_ext ?_
    simp only [quotientMapOfLE_π, Category.comp_id]
  map_comp {i j k} f g := by
    refine coequalizer.hom_ext ?_
    rw [quotientMapOfLE_π, ← Category.assoc, quotientMapOfLE_π,
      quotientMapOfLE_π]

/-- The cone over the tower of ideal-power quotients given by the quotient projections. -/
public def adicQuotientCone {X : Scheme.{u}} (I : X.IdealSheafData) (F : X.Modules) :
    Cone (adicQuotientSystem I F) where
  pt := F
  π.app n := cokernel.π (C := X.Modules) (idealPowerMultiple I n.unop F).ι
  π.naturality i j h := by
    simpa [adicQuotientSystem] using
      (quotientMapOfLE_π (idealPowerMultiple_antitone I F (leOfHom h.unop))).symm

end Stacks.Algebraization

end
