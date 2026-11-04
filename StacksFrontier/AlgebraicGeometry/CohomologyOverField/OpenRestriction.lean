module

public import StacksFrontier.AlgebraicGeometry.CohomologyOverField.TopDegreeRestriction
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.ExceptionalAnnihilation
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.LocalCohomologyExcision
public import StacksFrontier.CategoryTheory.Abelian.RightDerivedPostcompose
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.CompositeRightDerivedFunctors

/-!
# The cohomology of a module over an open is the cohomology of its restriction

`AlgebraicGeometry.cohomologyOverFieldOnOpen k f U ℱ n` is the degree-`n` right derived functor
of *sections over `U`* of a module `ℱ` on `X`, with the `k`-action restricted along the structure
morphism. It is the target of the restriction map
`AlgebraicGeometry.cohomologyOverFieldRestrict`, whose surjectivity in the top degree is clause
(2) of [Stacks, Tag 0A3G]. This file identifies that group with
`AlgebraicGeometry.cohomologyOverField` of the restricted module `ℱ|_U` on the open subscheme
`U`, as `k`-vector spaces.

Writing `j : U ⟶ X` for the inclusion, sections over `U` on `X` *are* global sections on `U`
composed with restriction `j^{-1}`, up to the identification of the two section rings that act on
the result; `j^{-1}` is exact and preserves injectives ([Stacks, Tag 01E1]), so the right
derived functors agree ([Stacks, Tag 015Z]).

## Main results

The elided prefix is `AlgebraicGeometry`.

* `cohomologyOverFieldOnOpenIsoRestrict`: **the comparison**, `Hⁿ(U, ℱ) ≅ Hⁿ(U, ℱ|_U)` as
  `k`-vector spaces, for `U` an open of a scheme over `k`.
* `finiteDimensional_cohomologyOverField_restrict_of_finiteType`: for `X` of finite type over `k`
  with `dim X ≤ d`, finite-dimensionality of `Hᵈ(X, ℱ)` passes to `Hᵈ(U, ℱ|_U)` for every
  quasi-compact open `U`, by clause (2) of [Stacks, Tag 0A3G].

## Implementation notes

The three generic inputs are `CategoryTheory.Functor.rightDerivedCompIso`, which pulls the
exact functor `ModuleCat.restrictScalars` out of a right derived functor,
`Stacks.Cohomology.CompositeRightDerived.rightDerivedNatIso`, which derives a natural
isomorphism, and `Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso`, which is
[Stacks, Tag 015Z] for the exact injective-preserving functor `j^{-1}`. The exactness and
injectivity instances of `Scheme.Modules.restrictFunctor U.ι` are
`Stacks.Coherent.preservesFiniteLimits_restrictFunctor_opens` and
`Stacks.Perfect.LocalCohomologyExcision.restrictFunctor_preservesInjectiveObjects`.

## References

* [Stacks Project, Tag 01E1](https://stacks.math.columbia.edu/tag/01E1)
* [Stacks Project, Tag 015Z](https://stacks.math.columbia.edu/tag/015Z)
* [Stacks Project, Tag 0A3G](https://stacks.math.columbia.edu/tag/0A3G)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

universe u

variable (k : Type u) [Field k]

/-- **Sections over the open image, as a `k`-module, are the global sections of the restriction.**
For `j : X ⟶ Y` an open immersion and `g : Y ⟶ Spec k`, evaluating a module on `Y` at the open
`j ''ᵁ ⊤` and restricting scalars to `k` is the same as restricting the module along `j` and
taking its global sections as a `k`-module. The only content is that the two structure maps
`k ⟶ Γ(Y, j ''ᵁ ⊤)` and `k ⟶ Γ(X, ⊤)` agree under `Scheme.Hom.appIso`, which is
`AlgebraicGeometry.Scheme.Hom.appLE_comp_appLE`. -/
def sectionsRestrictFieldIso {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    (g : Y ⟶ Spec (.of k)) :
    SheafOfModules.evaluation Y.ringCatSheaf (op (j ''ᵁ ⊤)) ⋙
        ModuleCat.restrictScalars
          ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appLE ⊤ (j ''ᵁ ⊤) (by simp)).hom ≅
      Scheme.Modules.restrictFunctor j ⋙
        SheafOfModules.evaluation X.ringCatSheaf (op ⊤) ⋙
          ModuleCat.restrictScalars
            ((Scheme.ΓSpecIso (.of k)).inv ≫ (j ≫ g).appLE ⊤ ⊤ (by simp)).hom :=
  have h : (j.appIso ⊤).inv.hom.comp
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (j ≫ g).appLE ⊤ ⊤ (by simp)).hom =
      ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appLE ⊤ (j ''ᵁ ⊤) (by simp)).hom := by
    change (((Scheme.ΓSpecIso (.of k)).inv ≫ (j ≫ g).appLE ⊤ ⊤ (by simp)) ≫
      (j.appIso ⊤).inv).hom = _
    rw [← j.appLE_comp_appLE g ⊤ (j ''ᵁ ⊤) ⊤ (by simp) (by simp),
      ← Scheme.Hom.appIso_hom', Category.assoc, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  Functor.isoWhiskerLeft (SheafOfModules.evaluation Y.ringCatSheaf (op (j ''ᵁ ⊤)))
    (ModuleCat.restrictScalarsComp'
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (j ≫ g).appLE ⊤ ⊤ (by simp)).hom
      (j.appIso ⊤).inv.hom
      ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appLE ⊤ (j ''ᵁ ⊤) (by simp)).hom h.symm)

variable {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- **The comparison.** `Hⁿ(U, ℱ)` as a `k`-vector space — that is,
`AlgebraicGeometry.cohomologyOverFieldOnOpen`, the target of the restriction map of clause (2) of
[Stacks, Tag 0A3G] — is the degree-`n` cohomology over `k` of the restricted module `ℱ|_U` on the
open subscheme `U`.

The scalar restriction is pulled inside the derived functor on each side by
`CategoryTheory.Functor.rightDerivedCompIso`; in between, `sectionsRestrictFieldIso` rewrites
`k`-linear sections over `U` as `k`-linear global sections after `j^{-1}`, and
`Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso` is [Stacks, Tag 015Z] for the
exact, injective-preserving functor `j^{-1}` ([Stacks, Tag 01E1]). -/
def cohomologyOverFieldOnOpenIsoRestrict (U : X.Opens) (F : X.Modules) (n : ℕ) :
    cohomologyOverFieldOnOpen k f U F n ≅
      cohomologyOverField k (U.ι ≫ f) ((Scheme.Modules.restrictFunctor U.ι).obj F) n :=
  have hU : U.ι ''ᵁ ⊤ = U := by simp
  have hV : (U.ι ''ᵁ ⊤ : X.Opens) ≤ f ⁻¹ᵁ ⊤ := by simp
  have hT : (⊤ : U.toScheme.Opens) ≤ (U.ι ≫ f) ⁻¹ᵁ ⊤ := by simp
  have hEY : (SheafOfModules.evaluation X.ringCatSheaf (op (U.ι ''ᵁ ⊤))).Additive := by
    unfold SheafOfModules.evaluation
    infer_instance
  have hEX : (SheafOfModules.evaluation U.toScheme.ringCatSheaf
      (op (⊤ : U.toScheme.Opens))).Additive := by
    unfold SheafOfModules.evaluation
    infer_instance
  have hL : (Scheme.Modules.restrictFunctor U.ι).Additive :=
    Functor.additive_of_preserves_binary_products _
  have hEYrY : (SheafOfModules.evaluation X.ringCatSheaf (op (U.ι ''ᵁ ⊤)) ⋙
      ModuleCat.restrictScalars
        ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ (U.ι ''ᵁ ⊤) hV).hom).Additive :=
    ⟨by intros; rfl⟩
  have hEXrX : (SheafOfModules.evaluation U.toScheme.ringCatSheaf (op (⊤ : U.toScheme.Opens)) ⋙
      ModuleCat.restrictScalars
        ((Scheme.ΓSpecIso (.of k)).inv ≫ (U.ι ≫ f).appLE ⊤ ⊤ hT).hom).Additive :=
    ⟨by intros; rfl⟩
  have hrY : (ModuleCat.restrictScalars
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ (U.ι ''ᵁ ⊤) hV).hom).Additive :=
    Functor.additive_of_preserves_binary_products _
  have hrX : (ModuleCat.restrictScalars
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (U.ι ≫ f).appLE ⊤ ⊤ hT).hom).Additive :=
    Functor.additive_of_preserves_binary_products _
  have hrYh : (ModuleCat.restrictScalars
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ (U.ι ''ᵁ ⊤) hV).hom).PreservesHomology :=
    have := hrY
    Functor.preservesHomologyOfExact _
  have hrXh : (ModuleCat.restrictScalars
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (U.ι ≫ f).appLE ⊤ ⊤ hT).hom).PreservesHomology :=
    have := hrX
    Functor.preservesHomologyOfExact _
  have hLEXrX : (Scheme.Modules.restrictFunctor U.ι ⋙
      (SheafOfModules.evaluation U.toScheme.ringCatSheaf (op (⊤ : U.toScheme.Opens)) ⋙
        ModuleCat.restrictScalars
          ((Scheme.ΓSpecIso (.of k)).inv ≫ (U.ι ≫ f).appLE ⊤ ⊤ hT).hom)).Additive :=
    ⟨fun {_ _ _ _} => by
      simp only [Functor.comp_map]
      rw [hL.map_add]
      exact hEXrX.map_add⟩
  eqToIso (congrArg (fun V : X.Opens =>
      (ModuleCat.restrictScalars
          ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ V (by simp)).hom).obj
        (((SheafOfModules.evaluation X.ringCatSheaf (op V)).rightDerived n).obj F)) hU.symm) ≪≫
    ((@Functor.rightDerivedCompIso _ _ _ _ _ _ _ _ _ _
      (SheafOfModules.evaluation X.ringCatSheaf (op (U.ι ''ᵁ ⊤))) hEY
      (ModuleCat.restrictScalars
        ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ (U.ι ''ᵁ ⊤) hV).hom) hrY hrYh n).app F).symm ≪≫
    (@Stacks.Cohomology.CompositeRightDerived.rightDerivedNatIso _ _ _ _ _ _ _ _ _ hEYrY hLEXrX
      (sectionsRestrictFieldIso k U.ι f) n).app F ≪≫
    (@Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso _ _ _ _ _ _ _ _ _ _ _
      (Scheme.Modules.restrictFunctor U.ι)
      (SheafOfModules.evaluation U.toScheme.ringCatSheaf (op (⊤ : U.toScheme.Opens)) ⋙
        ModuleCat.restrictScalars
          ((Scheme.ΓSpecIso (.of k)).inv ≫ (U.ι ≫ f).appLE ⊤ ⊤ hT).hom) hL hEXrX
      (Stacks.Coherent.preservesFiniteLimits_restrictFunctor_opens U)
      inferInstance inferInstance n).app F ≪≫
    (@Functor.rightDerivedCompIso _ _ _ _ _ _ _ _ _ _
      (SheafOfModules.evaluation U.toScheme.ringCatSheaf (op (⊤ : U.toScheme.Opens))) hEX
      (ModuleCat.restrictScalars
        ((Scheme.ΓSpecIso (.of k)).inv ≫ (U.ι ≫ f).appLE ⊤ ⊤ hT).hom) hrX hrXh n).app
      ((Scheme.Modules.restrictFunctor U.ι).obj F)

/-- **Finiteness passes from a scheme to a quasi-compact open in the top degree.** Let `X` be of
finite type over a field `k` with `dim X ≤ d`, let `ℱ` be any `𝒪_X`-module with `Hᵈ(X, ℱ)`
finite-dimensional and let `U ⊆ X` be a quasi-compact open. Then `Hᵈ(U, ℱ|_U)` is
finite-dimensional.

Clause (2) of [Stacks, Tag 0A3G], in the form
`AlgebraicGeometry.surjective_cohomologyOverFieldRestrict_of_finiteType`, makes the `k`-linear
restriction `Hᵈ(X, ℱ) ⟶ Hᵈ(U, ℱ)` surjective, `cohomologyOverFieldOnOpenIsoRestrict` identifies
its target with `Hᵈ(U, ℱ|_U)`, and a surjection out of a finite-dimensional space has
finite-dimensional target. -/
theorem finiteDimensional_cohomologyOverField_restrict_of_finiteType
    [LocallyOfFiniteType f] [QuasiCompact f] (F : X.Modules) (d : ℕ)
    (hdim : topologicalKrullDim (X : Type u) ≤ (d : WithBot ℕ∞))
    (U : X.Opens) (hU : IsCompact (U : Set X))
    (hfin : FiniteDimensional k (cohomologyOverField k f F d)) :
    FiniteDimensional k
      (cohomologyOverField k (U.ι ≫ f) ((Scheme.Modules.restrictFunctor U.ι).obj F) d) := by
  have hsurj : Function.Surjective (cohomologyOverFieldRestrict k f U F d ≫
      (cohomologyOverFieldOnOpenIsoRestrict k f U F d).hom) := by
    intro z
    obtain ⟨x, hx⟩ := surjective_cohomologyOverFieldRestrict_of_finiteType k f F d hdim U hU
      ((cohomologyOverFieldOnOpenIsoRestrict k f U F d).inv z)
    exact ⟨x, by rw [ConcreteCategory.comp_apply, hx]; simp⟩
  exact Module.Finite.of_surjective
    (cohomologyOverFieldRestrict k f U F d ≫
      (cohomologyOverFieldOnOpenIsoRestrict k f U F d).hom).hom hsurj

end AlgebraicGeometry

end
