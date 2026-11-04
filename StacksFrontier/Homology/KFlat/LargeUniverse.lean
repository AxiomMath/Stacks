module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import StacksFrontier.Algebra.Category.ModuleCat.Monoidal.LargeUniverse
public import StacksFrontier.Algebra.Homology.KFlat
public import StacksFrontier.Homology.TensorComplex.Monoidal

@[expose] public noncomputable section

/-!
# K-flatness and change of scalars above the ring universe

Several Chapter 15 statements need K-flatness and change of scalars for complexes whose modules
inhabit a universe above the ring's: a derived tensor product along a ring map `R → A` has to
accommodate the modules of both rings at once, so the module universe is `max v uR uA` and is
independent of either ring.

K-flatness at that generality is `CochainComplex.KFlat` itself, in
`StacksFrontier.Algebra.Homology.KFlat` — the central definition is stated at a module universe
`max u v` independent of the ring's and carries tag 06XZ. This file supplies the rest of what
the large-universe setting needs: the tensor-total functors, and the degreewise extension and
restriction of scalars on complexes at two independent ring universes, with the transfer
principles for restriction — it neither creates nor destroys acyclicity or quasi-isomorphism,
because it changes no underlying abelian group and no differential.

## Main definitions

* `CochainComplex.tensorLeftLarge`, `CochainComplex.tensorRightLarge`: tensoring a complex on
  either side and totalizing, at a module universe above the ring's.
* `CochainComplex.extendScalarsLarge`, `CochainComplex.restrictScalarsLarge`: change of scalars
  along `f : R →+* A` on complexes whose modules are large enough for both rings.

## Main results

* `CochainComplex.restrictScalarsLarge_acyclic_iff` and
  `CochainComplex.quasiIso_restrictScalarsLarge_map_iff`: restriction of scalars reflects and
  preserves acyclicity and quasi-isomorphism.

## Implementation notes

Cluster 09 of the Chapter 15 integration (sections 57-64) owns this module together with
`StacksFrontier.Algebra.Category.ModuleCat.Monoidal.LargeUniverse`, which supplies the lifted
monoidal structure that makes the two-universe setting possible at all — Mathlib's `ModuleCat`
monoidal instance takes the tensor unit to be `R`, so it exists only when the module universe
agrees with the ring's; the lifted structure takes the unit to be `ULift.{v} R`.

K-flatness is deliberately **not** redeclared here. This module once carried a second predicate
`KFlatLarge` for the two-universe form, with a bridge `kFlatLarge_iff_kFlat` proved by
`Iff.rfl`; both were removed when the central definition was generalised to exactly that form.
Two spellings of one notion joined by a bridge is worse than either spelling alone, because the
bridge is what lets the duplication survive indefinitely. If a further copy of this notion
turns up elsewhere in the tree, it is a duplicate and should be deleted in favour of importing
the central definition.

`extendScalarsLarge` supplies the `Additive` instance for `ModuleCat.extendScalars` by hand.
Mathlib derives additivity of `extendScalars` from the algebra structure, which is not
available from a bare ring homomorphism, so the instance is built from `f.toAlgebra` locally and
`mapHomologicalComplex` is applied to the result.

The acyclicity and quasi-isomorphism transfers are `rfl` after unfolding to short complexes of
abelian groups: `ModuleCat.restrictScalars` is the identity on carriers.
-/

open CategoryTheory MonoidalCategory
open scoped TensorProduct ChangeOfRings

universe u v uR uA

namespace CochainComplex

section KFlat

variable {R : Type u} [CommRing R]

/-! K-flatness itself is **not** declared here. It is `CochainComplex.KFlat` in
`StacksFrontier.Algebra.Homology.KFlat`, stated there at a module universe `max u v` independent
of the ring's and carrying tag 06XZ, and that is the tree's single definition of the notion.

This module previously declared a second predicate, `KFlatLarge`, for the two-universe form,
together with a bridge `kFlatLarge_iff_kFlat` proved by `Iff.rfl`. Both are gone: the central
definition was generalised to exactly the two-universe form, so the second predicate became a
duplicate spelling of one notion rather than a distinct statement, and a bridge between two
spellings is the thing that makes such a duplication permanent. Consumers use
`CochainComplex.KFlat` directly. -/

/-- Tensoring on the left with `N` and totalizing, on complexes of `R`-modules in a universe
above the ring's. -/
abbrev tensorLeftLarge (N : CochainComplex (ModuleCat.{max u v} R) ℤ) :=
  letI := ModuleCat.liftedModuleMonoidalStruct.{u, v} (R := R)
  letI := ModuleCat.liftedModuleMonoidal.{u, v} (R := R)
  TleftCochain N

/-- Tensoring on the right with `N` and totalizing, on complexes of `R`-modules in a universe
above the ring's. -/
abbrev tensorRightLarge (N : CochainComplex (ModuleCat.{max u v} R) ℤ) :=
  letI := ModuleCat.liftedModuleMonoidalStruct.{u, v} (R := R)
  letI := ModuleCat.liftedModuleMonoidal.{u, v} (R := R)
  TrightCochain N

end KFlat

section ChangeOfScalars

variable {R : Type uR} {A : Type uA} [CommRing R] [CommRing A]

/-- Degreewise extension of scalars along `f : R →+* A` on complexes, at any module universe
large enough to hold the modules of both rings. -/
def extendScalarsLarge (f : R →+* A) :
    CochainComplex (ModuleCat.{max v uR uA} R) ℤ ⥤
      CochainComplex (ModuleCat.{max v uR uA} A) ℤ :=
  letI : (ModuleCat.extendScalars.{uR, uA, max v uR uA} f).Additive := by
    let _ := f.toAlgebra
    refine ⟨fun {_ _ a b} => ?_⟩
    ext x
    change (1 : A) ⊗ₜ[R,f] ((a + b) x) =
      (1 : A) ⊗ₜ[R,f] a x + (1 : A) ⊗ₜ[R,f] b x
    exact TensorProduct.tmul_add _ _ _
  (ModuleCat.extendScalars.{uR, uA, max v uR uA} f).mapHomologicalComplex
    (ComplexShape.up ℤ)

/-- Degreewise restriction of scalars along `f : R →+* A` on complexes, at any module universe
large enough to hold the modules of both rings. It changes neither the underlying abelian
groups nor the differentials. -/
def restrictScalarsLarge (f : R →+* A) :
    CochainComplex (ModuleCat.{max v uR uA} A) ℤ ⥤
      CochainComplex (ModuleCat.{max v uR uA} R) ℤ :=
  (ModuleCat.restrictScalars.{max v uR uA} f).mapHomologicalComplex
    (ComplexShape.up ℤ)

/-- Restriction of scalars both preserves and reflects acyclicity: in each degree the short
complex whose exactness is at stake has the same underlying maps of abelian groups before and
after restriction. -/
theorem restrictScalarsLarge_acyclic_iff (f : R →+* A)
    (K : CochainComplex (ModuleCat.{max v uR uA} A) ℤ) :
    ((restrictScalarsLarge.{v} f).obj K).Acyclic ↔ K.Acyclic := by
  refine forall_congr' fun i => ?_
  rw [HomologicalComplex.exactAt_iff, HomologicalComplex.exactAt_iff,
    ShortComplex.moduleCat_exact_iff, ShortComplex.moduleCat_exact_iff]
  rfl

/-- Restriction of scalars both preserves and reflects quasi-isomorphism: it preserves
homology, being the identity on carriers. -/
theorem quasiIso_restrictScalarsLarge_map_iff (f : R →+* A)
    {K L : CochainComplex (ModuleCat.{max v uR uA} A) ℤ} (g : K ⟶ L) :
    QuasiIso ((restrictScalarsLarge.{v} f).map g) ↔ QuasiIso g :=
  HomologicalComplex.quasiIso_map_iff_of_preservesHomology g
    (ModuleCat.restrictScalars.{max v uR uA} f)

end ChangeOfScalars

end CochainComplex

end
