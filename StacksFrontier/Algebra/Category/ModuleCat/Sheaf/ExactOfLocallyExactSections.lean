module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# A short complex of sheaves of modules which is locally exact on sections is exact

Let `S : M₁ ⟶ M₂ ⟶ M₃` be a short complex of sheaves of modules on a site. If every section of
`M₂` killed by the second map is, locally, in the image of the first one, then `S` is exact: the
map from `M₁` onto the cycles of `S` is locally surjective on sections, hence an epimorphism of
sheaves of modules. The universe of the module sections is arbitrary.

## Main results

* `SheafOfModules.exact_of_locally_exists_preimage`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u u' t

namespace SheafOfModules

variable {C : Type u'} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasSheafify J AddCommGrpCat.{t}] [J.WEqualsLocallyBijective AddCommGrpCat.{t}]

/-- **A short complex of sheaves of modules which is locally exact on sections is exact.** If
for every object `T` and every section `x` of `M₂` over `T` killed by `S.g` there is a covering
sieve of `T` along whose arrows the restriction of `x` comes from a section of `M₁`, then `S` is
exact. -/
theorem exact_of_locally_exists_preimage (S : ShortComplex (SheafOfModules.{t} R))
    (h : ∀ (T : C) (x : S.X₂.val.obj (op T)), S.g.val.app (op T) x = 0 →
      ∃ U ∈ J T, ∀ ⦃V : C⦄ (a : V ⟶ T), U a →
        ∃ y : S.X₁.val.obj (op V), S.f.val.app (op V) y = S.X₂.val.map a.op x) :
    S.Exact := by
  rw [ShortComplex.exact_iff_epi_toCycles]
  have hmono : ∀ T : Cᵒᵖ, Function.Injective (S.iCycles.val.app T) := fun T => by
    have : Mono S.iCycles := inferInstance
    have h1 : Mono ((SheafOfModules.forget R).map S.iCycles) := inferInstance
    have h2 : Mono (((SheafOfModules.forget R).map S.iCycles).app T) := inferInstance
    exact (ModuleCat.mono_iff_injective _).1 h2
  refine Stacks.SheafOfModules.EpiMono.epi_of_isLocallySurjective _ ⟨fun {T} s => ?_⟩
  obtain ⟨U, hU, hloc⟩ := h T (S.iCycles.val.app (op T) s) (by
    change (S.iCycles ≫ S.g).val.app (op T) s = 0
    rw [S.iCycles_g]
    rfl)
  refine J.superset_covering (fun V a ha => ?_) hU
  obtain ⟨y, hy⟩ := hloc a ha
  refine ⟨y, hmono (op V) ?_⟩
  change (S.toCycles ≫ S.iCycles).val.app (op V) y = _
  rw [S.toCycles_i, hy]
  exact (ConcreteCategory.congr_hom (S.iCycles.val.naturality a.op) s).symm

end SheafOfModules
