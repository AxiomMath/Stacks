module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Abelian.Subcategory
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowSerreImage
public import StacksFrontier.Algebra.Homology.DerivedCategory.KGroup
public import StacksFrontier.AlgebraicGeometry.Perfect.CoherentDerivedCategory
public import StacksFrontier.CategoryTheory.Abelian.GrothendieckGroup
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Coherent sheaves on a scheme and their Grothendieck group

The category of coherent sheaves of modules on a scheme is abelian. Its zeroth Grothendieck group
is the group `K'₀(X)`.

## Main definitions

* `AlgebraicGeometry.CoherentKZero` is `K'₀(X)`.

## Main results

* `AlgebraicGeometry.coherentModulesAbelian` gives the abelian category structure on coherent
  modules over a scheme.
* `AlgebraicGeometry.exists_addEquiv_coherentKZero_K0`: the group `K'₀(X)` is the zeroth `K`-group
  of the bounded objects of `D(𝒪_X)` with coherent cohomology sheaves, by an isomorphism sending
  the class of a coherent sheaf to its class in degree `0`.

## Implementation notes

The category of coherent modules is the full subcategory of sheaves of modules cut out by
coherence, and `CoherentKZero` is `KZero` specialized to that category.

The source introduces `K'₀(X)` for a locally Noetherian `X`. That hypothesis is not used by
anything here and is therefore not assumed: coherence is the condition of Tag 01BV, which is
defined over an arbitrary ringed space, and the abelian structure on the coherent modules is Tag
01Y0, which holds over an arbitrary ringed space too
(`Stacks.SheafOfModules.coherentModulesAbelian`). For locally Noetherian `X` the group defined here
is the source's `K'₀(X)`.

## References

* [Stacks Project, Tag 0FDG](https://stacks.math.columbia.edu/tag/0FDG)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u d

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 0FDG.** Coherent sheaves of modules on a scheme form an abelian
category. -/
@[stacks 0FDG "coherent_abelian", sga "6 II 2.2.1" "Coh(S) abelian"]
noncomputable instance coherentModulesAbelian (X : Scheme.{u}) :
    Abelian (Stacks.SheafOfModules.CoherentModules X.ringCatSheaf) :=
  Stacks.SheafOfModules.coherentModulesAbelian X.ringCatSheaf

/-- **Stacks Project, Tag 0FDG (2).** The Grothendieck group `K'₀(X)` of coherent sheaves on a
scheme `X`. -/
@[stacks 0FDG "coherent_k0", sga "6 X 1.1", sga "6 IV 2.2" "K_•(A_X)_naif"]
noncomputable abbrev CoherentKZero (X : Scheme.{u}) : Type _ :=
  KZero (Stacks.SheafOfModules.CoherentModules X.ringCatSheaf)

/-- **Stacks Project, Tag 0FDF.** The Grothendieck group `K'₀(X)` of coherent sheaves on a scheme
`X` is the zeroth `K`-group of `D^b_Coh(𝒪_X)`, the bounded objects of `D(𝒪_X)` with coherent
cohomology sheaves, by an isomorphism sending the class of a coherent sheaf to the class of that
sheaf placed in degree `0`; and that property determines it. -/
@[stacks 0FDF "the identification K₀(Coh(𝒪_X)) = K₀(D^b_Coh(𝒪_X)), the source's second \
equality. The source's middle group K₀(D^b(Coh(𝒪_X))) is \
`AlgebraicGeometry.exists_addEquiv_coherentKZero_K0_bounded`",
  sga "6 IV 2.4" "special case",
  sga "6 IV 3.2.3" "more general"]
theorem exists_addEquiv_coherentKZero_K0 (X : Scheme.{u})
    [HasDerivedCategory.{d} (SheafOfModules.{u} X.ringCatSheaf)] :
    ∃ e : CoherentKZero X ≃+ Pretriangulated.K0 (DerivedCategoryB.derivedCategoryBBounded
        (Stacks.SheafOfModules.coherentModules X.ringCatSheaf)).FullSubcategory,
      (∀ F : Stacks.SheafOfModules.CoherentModules X.ringCatSheaf,
          ∃ K : (DerivedCategoryB.derivedCategoryBBounded
              (Stacks.SheafOfModules.coherentModules X.ringCatSheaf)).FullSubcategory,
            Nonempty (K.obj ≅ (DerivedCategory.singleFunctor
              (SheafOfModules.{u} X.ringCatSheaf) 0).obj F.obj)) ∧
        ∀ (F : Stacks.SheafOfModules.CoherentModules X.ringCatSheaf)
          (K : (DerivedCategoryB.derivedCategoryBBounded
              (Stacks.SheafOfModules.coherentModules X.ringCatSheaf)).FullSubcategory),
          (K.obj ≅ (DerivedCategory.singleFunctor
              (SheafOfModules.{u} X.ringCatSheaf) 0).obj F.obj) →
            e (KZero.mk _ F) = QuotientAddGroup.mk (FreeAbelianGroup.of K) :=
  DerivedCategory.exists_addEquiv_K0_of_isWeakSerreClass _
    (DerivedCategoryB.derivedCategoryBBounded_eq_bounded_inf _)

end AlgebraicGeometry
