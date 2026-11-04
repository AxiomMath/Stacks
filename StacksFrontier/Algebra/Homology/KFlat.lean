module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
public import Mathlib.Tactic.CrossRefAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Monoidal.LargeUniverse
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

/-!
# K-flat complexes of modules

Let `R` be a commutative ring. A cochain complex `K` of `R`-modules is *K-flat* when the
total complex `Tot(M ⊗_R K)` is acyclic for every acyclic cochain complex `M` of
`R`-modules. This file introduces that property, `CochainComplex.KFlat`, together with the
change-of-rings functors on cochain complexes, and shows that acyclicity is invariant under
isomorphism of complexes and that restriction of scalars along a ring map both preserves and
reflects it.

## Main definitions

* `CochainComplex.KFlat`: K-flatness of a cochain complex of modules.
* `CochainComplex.restrictScalars` and `CochainComplex.extendScalars`: restriction and extension
  of scalars along a ring map, degreewise.

## Main results

* `HomologicalComplex.Acyclic.of_iso`: a complex isomorphic to an acyclic complex is acyclic.
* `CochainComplex.restrictScalars_acyclic_iff`: restriction of scalars preserves and reflects
  acyclicity.
-/

open CategoryTheory MonoidalCategory

universe u v

variable {R R' : Type u} [CommRing R] [CommRing R']

/-- A cochain complex `K` of `R`-modules is *K-flat* if the total complex `Tot(M ⊗_R K)` is
acyclic for every acyclic cochain complex `M` of `R`-modules. Here `⊗` is the monoidal product of
cochain complexes, i.e. the total complex of the tensor product double complex with the Koszul
sign convention. -/
@[stacks 06XZ]
def CochainComplex.KFlat (K : CochainComplex (ModuleCat.{max u v} R) ℤ) : Prop :=
  letI := ModuleCat.liftedModuleMonoidalStruct.{u, v} (R := R)
  letI := ModuleCat.liftedModuleMonoidal.{u, v} (R := R)
  ∀ M : CochainComplex (ModuleCat.{max u v} R) ℤ,
    M.Acyclic → (HomologicalComplex.tensorObj M K).Acyclic

/-- A complex isomorphic to an acyclic complex is acyclic. -/
theorem HomologicalComplex.Acyclic.of_iso {M N : CochainComplex (ModuleCat.{v} R) ℤ}
    (e : M ≅ N) (h : M.Acyclic) : N.Acyclic :=
  fun i ↦ HomologicalComplex.ExactAt.of_iso (h i) e

/-- Restriction of scalars on cochain complexes along a ring map `φ : R →+* R'`: a complex of
`R'`-modules regarded as a complex of `R`-modules, with `r` acting as `φ r`. It applies
`ModuleCat.restrictScalars φ` in each degree, so it changes neither the underlying abelian
groups nor the differentials. -/
@[ega "III 6.3.10"]
noncomputable def CochainComplex.restrictScalars (φ : R →+* R') :
    CochainComplex (ModuleCat R') ℤ ⥤ CochainComplex (ModuleCat R) ℤ :=
  (ModuleCat.restrictScalars φ).mapHomologicalComplex (ComplexShape.up ℤ)

/-- Extension of scalars on cochain complexes along a ring map `φ : R →+* R'`: a complex of
`R`-modules base-changed to `R'`, applying `ModuleCat.extendScalars φ`, that is `R' ⊗[R] -`, in
each degree. -/
@[ega "III 7.4.1"]
noncomputable def CochainComplex.extendScalars (φ : R →+* R') :
    CochainComplex (ModuleCat R) ℤ ⥤ CochainComplex (ModuleCat R') ℤ :=
  (ModuleCat.extendScalars φ).mapHomologicalComplex (ComplexShape.up ℤ)

/-- Restriction of scalars along a ring map both preserves and reflects acyclicity. -/
theorem CochainComplex.restrictScalars_acyclic_iff (φ : R →+* R')
    (L : CochainComplex (ModuleCat R') ℤ) :
    ((CochainComplex.restrictScalars φ).obj L).Acyclic ↔ L.Acyclic := by
  refine forall_congr' fun i ↦ ?_
  rw [HomologicalComplex.exactAt_iff, HomologicalComplex.exactAt_iff,
    ShortComplex.moduleCat_exact_iff, ShortComplex.moduleCat_exact_iff]
  rfl
