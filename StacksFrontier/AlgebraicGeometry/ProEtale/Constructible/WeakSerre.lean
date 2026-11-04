module

public import StacksFrontier.AlgebraicGeometry.ProEtale.Constructible.InverseImage
public import StacksFrontier.AlgebraicGeometry.ProEtale.Constructible.StratificationSupplement
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyConstantExtensions
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.AbelianWeakSerre
import StacksCore.Tactic.StacksAttribute

/-!
# Constructible pro-étale sheaves form a weak Serre subcategory

Let `X` be a scheme and `Λ` a Noetherian ring. The constructible sheaves of `Λ`-modules on the
small pro-étale site of `X`, `AlgebraicGeometry.ProEtale.IsConstructibleModuleSheaf'`, form a
weak Serre subcategory of all sheaves of `Λ`-modules on that site.

## Main results

* `AlgebraicGeometry.ProEtale.exists_stratification_forall`: finitely many constructible sheaves
  are simultaneously locally constant of finite type on the strata of one constructible
  partition of each affine open.
* `AlgebraicGeometry.ProEtale.isWeakSerreClass_isConstructibleModuleSheaf'`: the weak Serre
  property.

## Implementation notes

The proof is the one of the étale statement, Tag 03RZ (3), carried out on the pro-étale site,
rather than the deduction of the source from the étale statement through the equivalence of
Tag 09AK and the weak Serre property of the essential image of `ε⁻¹` (Tag 09B1). The weak Serre
condition is tested in its five term form,
`CategoryTheory.ObjectProperty.isWeakSerreClass_iff_prop_obj₂_of_exact`: given an exact sequence
`ℱ₀ ⟶ ℱ₁ ⟶ ℱ₂ ⟶ ℱ₃ ⟶ ℱ₄` whose four outer terms are constructible, an affine open of `X` is
partitioned so that the four outer terms are locally constant of finite type on every stratum.
Inverse image to a stratum is exact, so the restricted sequence is exact, and the sheaves locally
constant of finite type on a site form a weak Serre subcategory (Tag 093U (3)), so the
restriction of `ℱ₂` to every stratum is locally constant of finite type.

The common partition is a common refinement of the four given ones,
`AlgebraicGeometry.Scheme.ConstructibleStratification.exists_refines_forall`. On a refined
stratum the restriction of a sheaf is the inverse image, along the immersion of the stratum into
the coarser one, of its restriction to the coarser stratum, up to the canonical isomorphism
`AlgebraicGeometry.ProEtale.proetaleModuleInverseImageCompIso`, and inverse image preserves local
constancy of finite type.

## References

* [Stacks Project, Tag 09B5](https://stacks.math.columbia.edu/tag/09B5)
* [Stacks Project, Tag 09AJ](https://stacks.math.columbia.edu/tag/09AJ)
* [Stacks Project, Tag 03RZ](https://stacks.math.columbia.edu/tag/03RZ)
* [Stacks Project, Tag 093U](https://stacks.math.columbia.edu/tag/093U)
* [Stacks Project, Tag 0754](https://stacks.math.columbia.edu/tag/0754)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.ConstantSheaf
open scoped ZeroObject

universe u v w

namespace AlgebraicGeometry.ProEtale

variable {X : Scheme.{u}} {Λ : Type v} [CommRing Λ]

/-- **Local constancy of finite type passes to a refinement.** If the restriction of `F` to every
stratum of `s` is locally constant of finite type, then so is its restriction to every stratum of
a refinement `r` of `s`. -/
public theorem isFiniteTypeLocallyConstantModuleSheaf_of_refines {U : X.Opens}
    {r s : Scheme.ConstructibleStratification X U} (hrs : r.Refines s)
    {F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) v w} Λ)}
    (hs : ∀ i, IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, max v w, v}
      (Scheme.ProEt.topology (s.piece i)) Λ
      ((proetaleModuleInverseImage.{u, v, w} (s.inclusion i) Λ).obj F))
    (k : Fin r.n) :
    IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, max v w, v}
      (Scheme.ProEt.topology (r.piece k)) Λ
      ((proetaleModuleInverseImage.{u, v, w} (r.inclusion k) Λ).obj F) := by
  obtain ⟨i, a, -, hfac⟩ := hrs k
  rw [← hfac]
  exact ObjectProperty.prop_of_iso _
    ((proetaleModuleInverseImageCompIso.{u, v, w} Λ a (s.inclusion i)).app F)
    (isFiniteTypeLocallyConstantModuleSheaf_proetaleModuleInverseImage a _ (hs i))

variable [IsNoetherianRing Λ]

/-- **Finitely many constructible sheaves on one partition.** Given finitely many constructible
sheaves of `Λ`-modules on the small pro-étale site of `X`, every affine open of `X` has a single
partition into constructible locally closed subschemes on each of whose strata all of them are
locally constant of finite type. -/
public theorem exists_stratification_forall {n : ℕ}
    {F : Fin n → Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) v w} Λ)}
    (hF : ∀ j, IsConstructibleModuleSheaf'.{u, v, w} X Λ (F j)) (U : X.affineOpens) :
    ∃ r : Scheme.ConstructibleStratification X U.1, ∀ k j,
      IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, max v w, v}
        (Scheme.ProEt.topology (r.piece k)) Λ
        ((proetaleModuleInverseImage.{u, v, w} (r.inclusion k) Λ).obj (F j)) := by
  choose s hs using fun j => hF j U
  obtain ⟨r, hr⟩ := Scheme.ConstructibleStratification.exists_refines_forall s
  exact ⟨r, fun k j => isFiniteTypeLocallyConstantModuleSheaf_of_refines (hr j) (hs j) k⟩

/-- A zero sheaf of `Λ`-modules on the small pro-étale site is constructible: its inverse image
to the single stratum of any affine open is zero, hence locally constant of finite type. -/
public theorem isConstructibleModuleSheaf'_of_isZero
    {F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) v w} Λ)} (hF : IsZero F) :
    IsConstructibleModuleSheaf'.{u, v, w} X Λ F := fun U =>
  ⟨Scheme.ConstructibleStratification.single X U.1, fun _ =>
    ObjectProperty.prop_of_isZero _ (Functor.map_isZero _ hF)⟩

variable (X Λ) in
/-- **Stacks 09B5.** For `Λ` a Noetherian ring, the constructible sheaves of `Λ`-modules on the
small pro-étale site of a scheme `X` form a weak Serre subcategory of all sheaves of
`Λ`-modules on that site. There is no hypothesis on `X`. -/
@[stacks 09B5]
public theorem isWeakSerreClass_isConstructibleModuleSheaf' :
    ObjectProperty.IsWeakSerreClass
      (fun F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) v w} Λ) =>
        IsConstructibleModuleSheaf'.{u, v, w} X Λ F) := by
  refine (ObjectProperty.isWeakSerreClass_iff_prop_obj₂_of_exact _).2
    ⟨⟨0, isConstructibleModuleSheaf'_of_isZero (isZero_zero _)⟩, ?_⟩
  intro S hS h₀ h₁ h₃ h₄ U
  obtain ⟨r, hr⟩ := exists_stratification_forall
    (F := ![S.obj' 0, S.obj' 1, S.obj' 3, S.obj' 4]) (fun j => by fin_cases j <;> assumption) U
  refine ⟨r, fun k => ?_⟩
  exact ObjectProperty.prop_obj₂_of_exact
    (P := IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, max v w, v}
      (Scheme.ProEt.topology (r.piece k)) Λ)
    (((proetaleModuleInverseImage.{u, v, w} (r.inclusion k) Λ).mapComposableArrows 4).obj S)
    (mapComposableArrows_exact _ S hS) (hr k 0) (hr k 1) (hr k 2) (hr k 3)

end AlgebraicGeometry.ProEtale

end
