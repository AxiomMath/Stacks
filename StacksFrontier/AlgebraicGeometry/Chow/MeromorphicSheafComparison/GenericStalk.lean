module

public import Mathlib.AlgebraicGeometry.FunctionField
public import StacksFrontier.AlgebraicGeometry.Chow.MeromorphicOrder.Stalk
public import StacksFrontier.AlgebraicGeometry.Chow.MeromorphicSheafComparison.Localization
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.AffineLocalization

/-!
# The generic stalk of a quasi-coherent module is a localization of any other stalk

Let `X` be an integral scheme with generic point `η` and let `F` be a quasi-coherent
`𝒪_X`-module. For a point `x` of `X` the specialization map `F_x → F_η` exhibits `F_η` as the
localization of `F_x` at the nonzerodivisors of the local ring `𝒪_{X, x}`; equivalently, as
`F_x ⊗_{𝒪_{X, x}} R(X)`.

## Main definitions

* `Stacks.Divisors.genericStalkModule` — the generic stalk `F_η` as a module over the local ring
  at a point, by restriction of scalars along the specialization map.
* `Stacks.Divisors.toGenericStalkₗ` — the specialization map `F_x → F_η`, as a linear map over
  the local ring at `x`.

## Main results

* `Stacks.Divisors.isLocalizedModule_toGenericStalkₗ` — the specialization map exhibits `F_η` as
  the localization of `F_x` at the nonzerodivisors of `𝒪_{X, x}`.

## References

* [Stacks Project, Tag 01X5](https://stacks.math.columbia.edu/tag/01X5)
* [Stacks Project, Tag 02OW](https://stacks.math.columbia.edu/tag/02OW)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry

universe u

namespace Stacks.Divisors

variable {X : Scheme.{u}}

/-- The generic point of an irreducible space lies in every nonempty open set. -/
theorem genericPoint_mem_of_nonempty [IrreducibleSpace X] (U : X.Opens) [Nonempty U] :
    genericPoint X ∈ U :=
  ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)

/-- The stalk of an `𝒪_X`-module at the generic point of an irreducible scheme, as a module over
the local ring at an arbitrary point: scalars act through the specialization map
`𝒪_{X, x} → R(X)`. -/
@[instance_reducible]
def genericStalkModule [IrreducibleSpace X] (F : X.Modules) (x : X) :
    Module (X.presheaf.stalk x) (F.presheaf.stalk (genericPoint X)) :=
  Module.compHom _ (X.presheaf.stalkSpecializes
    ((genericPoint_spec X).specializes trivial)).hom

/-- The specialization map `F_x → F_η` to the generic stalk, as a linear map over the local ring
at `x`. -/
def toGenericStalkₗ [IrreducibleSpace X] (F : X.Modules) (x : X) :
    letI := genericStalkModule F x
    F.presheaf.stalk x →ₗ[X.presheaf.stalk x] F.presheaf.stalk (genericPoint X) :=
  letI := genericStalkModule F x
  { toFun := F.presheaf.stalkSpecializes ((genericPoint_spec X).specializes trivial)
    map_add' := map_add _
    map_smul' := fun r m => Scheme.Modules.stalkSpecializes_smul F _ r m }

/-- The specialization map to the generic stalk sends the germ of a section at a point to its
germ at the generic point. -/
theorem toGenericStalkₗ_germ [IrreducibleSpace X] (F : X.Modules) (x : X) (U : X.Opens)
    (hx : x ∈ U) (hη : genericPoint X ∈ U) (s : Γ(F, U)) :
    toGenericStalkₗ F x (F.presheaf.germ U x hx s) = F.presheaf.germ U (genericPoint X) hη s := by
  show F.presheaf.stalkSpecializes _ (F.presheaf.germ U x hx s) = _
  exact TopCat.Presheaf.germ_stalkSpecializes_apply ..

/-- On an affine open of an integral scheme the complement of the prime corresponding to the
generic point is the set of nonzerodivisors of the ring of functions. -/
theorem primeCompl_genericPoint_eq_nonZeroDivisors [IsIntegral X] {U : X.Opens}
    (hU : IsAffineOpen U) [Nonempty U] :
    (hU.primeIdealOf ⟨genericPoint X, genericPoint_mem_of_nonempty U⟩).asIdeal.primeCompl =
      nonZeroDivisors Γ(X, U) := by
  have h : (hU.primeIdealOf ⟨genericPoint X, genericPoint_mem_of_nonempty U⟩).asIdeal
      = (⊥ : Ideal Γ(X, U)) := by
    rw [hU.primeIdealOf_genericPoint, genericPoint_eq_bot_of_affine]
    rfl
  ext a
  show a ∉ (hU.primeIdealOf ⟨genericPoint X, genericPoint_mem_of_nonempty U⟩).asIdeal ↔
    a ∈ nonZeroDivisors Γ(X, U)
  rw [h, Ideal.mem_bot, mem_nonZeroDivisors_iff_ne_zero]

/-- On an integral scheme the specialization map `F_x → F_η` of a quasi-coherent module exhibits
the generic stalk as the localization of the stalk at `x` at the nonzerodivisors of the local
ring there. -/
theorem isLocalizedModule_toGenericStalkₗ [IsIntegral X] (F : X.Modules) [F.IsQuasicoherent]
    (x : X) :
    letI := genericStalkModule F x
    IsLocalizedModule (nonZeroDivisors (X.presheaf.stalk x)) (toGenericStalkₗ F x) := by
  let := genericStalkModule F x
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
  have : Nonempty U := ⟨⟨x, hxU⟩⟩
  have hη : genericPoint X ∈ U := genericPoint_mem_of_nonempty U
  let p := (hU.primeIdealOf ⟨x, hxU⟩).asIdeal
  let : Algebra Γ(X, U) (X.presheaf.stalk x) := X.presheaf.algebra_section_stalk ⟨x, hxU⟩
  let : IsLocalization p.primeCompl (X.presheaf.stalk x) := hU.isLocalization_stalk ⟨x, hxU⟩
  let := affineStalkModule F U x hxU
  let := affineStalkModule F U (genericPoint X) hη
  let : IsScalarTower Γ(X, U) (X.presheaf.stalk x) (F.presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let : IsScalarTower Γ(X, U) (X.presheaf.stalk x)
      (F.presheaf.stalk (genericPoint X)) := by
    refine IsScalarTower.of_algebraMap_smul fun r z => ?_
    show (X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes trivial)).hom
        ((X.presheaf.germ U x hxU).hom r) • z = (X.presheaf.germ U (genericPoint X) hη).hom r • z
    rw [show (X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes trivial)).hom
        ((X.presheaf.germ U x hxU).hom r) = (X.presheaf.germ U (genericPoint X) hη).hom r from
      TopCat.Presheaf.germ_stalkSpecializes_apply ..]
  have hle : p.primeCompl ≤ nonZeroDivisors Γ(X, U) := fun a ha =>
    mem_nonZeroDivisors_iff_ne_zero.mpr fun h0 => ha (h0 ▸ Submodule.zero_mem p)
  have hsections : IsLocalizedModule (nonZeroDivisors Γ(X, U))
      ((toGenericStalkₗ F x).restrictScalars Γ(X, U)) := by
    have h1 : IsLocalizedModule p.primeCompl (affineGerm F U x hxU) :=
      affineGerm_isLocalized F U hU x hxU
    have h2 : IsLocalizedModule (nonZeroDivisors Γ(X, U))
        (affineGerm F U (genericPoint X) hη) := by
      rw [← primeCompl_genericPoint_eq_nonZeroDivisors hU]
      exact affineGerm_isLocalized F U hU (genericPoint X) hη
    exact Stacks.Localization.isLocalizedModule_of_comp hle (affineGerm F U x hxU)
      (affineGerm F U (genericPoint X) hη) _
      fun m => toGenericStalkₗ_germ F x U hxU hη m
  have hlocal : IsLocalizedModule
      (Algebra.algebraMapSubmonoid (X.presheaf.stalk x) (nonZeroDivisors Γ(X, U)))
      (toGenericStalkₗ F x) :=
    IsLocalizedModule.of_restrictScalars (nonZeroDivisors Γ(X, U)) (toGenericStalkₗ F x)
  have hinj : Function.Injective (algebraMap Γ(X, U) (X.presheaf.stalk x)) :=
    germ_injective_of_isIntegral X x hxU
  have hsub : Algebra.algebraMapSubmonoid (X.presheaf.stalk x) (nonZeroDivisors Γ(X, U)) ≤
      nonZeroDivisors (X.presheaf.stalk x) := by
    rintro - ⟨t, ht, rfl⟩
    refine mem_nonZeroDivisors_iff_ne_zero.mpr fun h0 => ?_
    exact (mem_nonZeroDivisors_iff_ne_zero.mp ht) (hinj (by rw [h0, map_zero]))
  have hmul : ∀ z : nonZeroDivisors (X.presheaf.stalk x), ∃ m : X.presheaf.stalk x,
      m * z.1 ∈ Algebra.algebraMapSubmonoid (X.presheaf.stalk x) (nonZeroDivisors Γ(X, U)) := by
    intro z
    obtain ⟨⟨b, s⟩, hbs⟩ := IsLocalization.surj p.primeCompl z.1
    refine ⟨algebraMap Γ(X, U) (X.presheaf.stalk x) s.1, ?_⟩
    have hb : b ≠ 0 := fun hb0 => mem_nonZeroDivisors_iff_ne_zero.mp z.2
      ((IsLocalization.map_units (M := p.primeCompl) (X.presheaf.stalk x) s).mul_right_eq_zero.mp
        (by rw [mul_comm, hbs, hb0, map_zero]))
    exact ⟨b, mem_nonZeroDivisors_iff_ne_zero.mpr hb, by rw [← hbs, mul_comm]⟩
  exact IsLocalizedModule.of_exists_mul_mem _ _ hsub hmul (toGenericStalkₗ F x)

end Stacks.Divisors
