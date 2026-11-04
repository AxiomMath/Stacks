module

public import StacksFrontier.AlgebraicGeometry.Descent.ZariskiHomAmalgamation
public import StacksFrontier.AlgebraicGeometry.ExternalTensorPullback.ComparisonSections
public import StacksFrontier.AlgebraicGeometry.GlobalSectionsOverField.Basic

/-!
# Sections over an open as a vector space over the ground field

`AlgebraicGeometry.globalSectionsOverField k f F` is `Γ(X, F)` regarded as a `k`-vector space for
a scheme `X` over `k`. This file records the same construction over an arbitrary open `U` of `X`,
together with the restriction maps between them, which are `k`-linear, and the statement that the
restrictions to the members of an open covering are *jointly injective*.

That last statement is the form in which the sheaf axiom enters a Künneth argument: an element of
`Γ(X, P) ⊗_k Γ(Y, Q)` is detected by its images in the `Γ(U, P) ⊗_k Γ(V, Q)` precisely because
each factor is detected by its restrictions, and detecting the tensor product needs the covering
to be finite (`TensorProduct.eq_zero_of_map_eq_zero_of_jointly_injective`).

## Main definitions

* `AlgebraicGeometry.sectionsOverField`: `Γ(U, F)` as a `k`-vector space. At `U = ⊤` it is
  `AlgebraicGeometry.globalSectionsOverField` on the nose, which is
  `AlgebraicGeometry.sectionsOverField_top`.
* `AlgebraicGeometry.sectionsOverFieldRestrict`: the restriction map, as a `k`-linear map.

## Main results

* `AlgebraicGeometry.sectionsScalars_restrict`: the ground-field structures on the sections over
  nested opens agree.
* `AlgebraicGeometry.sectionsOverFieldRestrict_apply`: it is the restriction map of the sheaf.
* `AlgebraicGeometry.eq_zero_of_sectionsOverFieldRestrict_eq_zero`: **a global section whose
  restriction to every member of an open covering vanishes is zero**.

## Implementation notes

The `k`-action is `ModuleCat.restrictScalars` along `k ⟶ Γ(X, ⊤) ⟶ Γ(X, U)`, written as the
single `AlgebraicGeometry.Scheme.Hom.appLE` of the structure morphism from `⊤` to `U`; the
`k`-linearity of restriction is then exactly `AlgebraicGeometry.Scheme.Hom.appLE_map`, which says
that composing that ring map with a further restriction is again such an `appLE`.

`AlgebraicGeometry.sectionsOverFieldRestrict` is a bare `LinearMap` between the carriers rather
than a morphism of `ModuleCat k`. Building it as `ModuleCat.ofHom` of a structure literal fails:
the expected type then forces `AlgebraicGeometry.sectionsOverField` open, and
`Module ↑(CommRingCat.of k) ↑((SheafOfModules.evaluation X.ringCatSheaf (op U)).obj F)` is not
found by instance search — `ModuleCat.restrictScalars` leaves the carrier untouched, so after
unfolding there is no `↑(M : ModuleCat k)` for the instance to key on. Left folded, the carriers
are exactly of that shape and the `k`-module structures are found.

The vanishing statement is `AlgebraicGeometry.section_eq_of_cover` at `V = ⊤`. That lemma
restricts to `⊤ ⊓ W i` rather than to `W i`, so the hypothesis has to be transported along the
factorisation of `⊤ ⊓ W i ⟶ ⊤` through `W i`, which is
`Stacks.Tag01VSPullbackTensor.presheaf_map_map`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Tag01VSPullbackTensor

universe u

namespace AlgebraicGeometry

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (F : X.Modules)

/-- The ring map making `Γ(X, U)` an algebra over the ground field. -/
abbrev sectionsScalars (U : X.Opens) : CommRingCat.of k ⟶ Γ(X, U) :=
  (Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ U le_top

/-- **The sections of `F` over `U`, as a vector space over the ground field.** -/
def sectionsOverField (U : X.Opens) : ModuleCat.{u} k :=
  (ModuleCat.restrictScalars
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ U le_top).hom).obj
    ((SheafOfModules.evaluation X.ringCatSheaf (op U)).obj F)

/-- Over `⊤` the sections as a `k`-vector space are
`AlgebraicGeometry.globalSectionsOverField`. -/
theorem sectionsOverField_top : sectionsOverField k f F ⊤ = globalSectionsOverField k f F := rfl

/-- The two ground-field structures on the sections over nested opens agree: `k ⟶ Γ(X, U)`
followed by restriction is `k ⟶ Γ(X, V)`. -/
theorem sectionsScalars_restrict {U V : X.Opens} (hVU : V ≤ U) (c : k) :
    X.presheaf.map (homOfLE hVU).op (sectionsScalars k f U c) = sectionsScalars k f V c := by
  have h2 : f.appLE ⊤ U le_top ≫ X.presheaf.map (homOfLE hVU).op = f.appLE ⊤ V le_top :=
    Scheme.Hom.appLE_map f le_top (homOfLE hVU).op
  have key : sectionsScalars k f U ≫ X.presheaf.map (homOfLE hVU).op = sectionsScalars k f V := by
    rw [sectionsScalars, Category.assoc, h2]
  exact (ConcreteCategory.comp_apply (sectionsScalars k f U)
    (X.presheaf.map (homOfLE hVU).op) c).symm.trans (ConcreteCategory.congr_hom key c)

/-- **Restriction of sections, as a `k`-linear map.** -/
def sectionsOverFieldRestrict {U V : X.Opens} (hVU : V ≤ U) :
    ↑(sectionsOverField k f F U) →ₗ[k] ↑(sectionsOverField k f F V) where
  toFun s := F.presheaf.map (homOfLE hVU).op s
  map_add' s s' := map_add _ s s'
  map_smul' c s :=
    (Scheme.Modules.map_smul (M := F) (homOfLE hVU) (sectionsScalars k f U c) s).trans
      (congrArg (fun r => r • F.presheaf.map (homOfLE hVU).op s)
        (sectionsScalars_restrict k f hVU c))

/-- The `k`-linear restriction map `AlgebraicGeometry.sectionsOverFieldRestrict` sends a section
`s` to its restriction `F.presheaf.map (homOfLE hVU).op s`. -/
@[simp] theorem sectionsOverFieldRestrict_apply {U V : X.Opens} (hVU : V ≤ U)
    (s : ↑(sectionsOverField k f F U)) :
    sectionsOverFieldRestrict k f F hVU s = F.presheaf.map (homOfLE hVU).op s := rfl

/-- **A global section whose restriction to every member of an open covering vanishes is zero.** -/
theorem eq_zero_of_sectionsOverFieldRestrict_eq_zero {ι : Type*} {W : ι → X.Opens}
    (hW : ⨆ i, W i = ⊤) (s : ↑(sectionsOverField k f F ⊤))
    (h : ∀ i, sectionsOverFieldRestrict k f F (le_top (a := W i)) s = 0) : s = 0 := by
  refine section_eq_of_cover hW s 0 fun i => ?_
  rw [map_zero]
  refine (presheaf_map_map F (homOfLE (le_top (a := W i)))
    (homOfLE (inf_le_right : ⊤ ⊓ W i ≤ W i))
    (homOfLE (inf_le_left : ⊤ ⊓ W i ≤ (⊤ : X.Opens))) s).symm.trans ?_
  rw [show F.presheaf.map (homOfLE (le_top (a := W i))).op s = 0 from h i, map_zero]

end AlgebraicGeometry

end
