module

public import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.HypercoveringModuleCohomologicalDescent
public import StacksFrontier.CategoryTheory.Sites.Simplicial.CartesianWeakSerreModules

/-!
# The class `A_total` on the total site of a simplicial site is a weak Serre subcategory

Let `S` be a simplicial-site situation and `O` a sheaf of commutative rings on its total site.
For a family `A_n` of weak Serre subcategories of the categories of modules on the simplicial
components, the class

`A_total ⊂ Mod(O)`

of cartesian `O`-modules `F` whose degreewise restriction `F_n = g_n^* F` lies in `A_n` is again
a weak Serre subcategory (the first assertion of Stacks 0DC7). The source's family is
`A_{K_n} = ∏_i A_{U_{n, i}}` for the semi-representable object `K_n = {U_{n, i}}`, which is one
such family.

## Main definitions

* `Stacks.Cohomology.CohomologicalDescent.cartesianDegreewiseModules`: the class `A_total`, the
  cartesian `O`-modules whose restriction to each simplicial component lies in the prescribed
  class there.

## Main results

* `Stacks.Cohomology.CohomologicalDescent.isWeakSerreClass_cartesianDegreewiseModules`:
  **Stacks 0DC7**, the assertion that `A_total` is a weak Serre subcategory.
* `Stacks.Cohomology.CohomologicalDescent`
  `.isWeakSerreClass_cartesianDegreewiseModules_hypercovering`: the same at the total ringed site
  `((C/K)_total, O)` of a hypercovering, with `O = a⁻¹O_C` the structure sheaf of Stacks 0D9W.

## Implementation notes

**The degreewise condition is restriction to a simplicial component**, the functor `g_n^*` of
Tag 0D72, which is `CategoryTheory.SimplicialSiteSituation.componentModuleRestriction`; the
source's `F_n` is exactly its value. The family `A_n` is therefore indexed by simplex objects
and lives on the component sheaves of rings.

**Cartesianness is the spelling of Stacks 07TF (2) through the transition of Tag 09WF**,
`CategoryTheory.SimplicialSiteSituation.IsCartesianModule`, because that is the spelling Tag
0D7J (2) is proved for in this library.

**The weak Serre property of the cartesian modules is a hypothesis of the shape Tag 0D7J (2)
hands it over**: left exactness `hflat` of the pullback of modules along the transition morphism
of each face map. That is weaker than flatness of the face transitions, which is what the source
assumes, so no generality is lost.

**The abelian structure, the sheafification instances and the exactness of `g_n^*`** are the
local instances of `StacksFrontier/CategoryTheory/Sites/Simplicial/CartesianWeakSerreModules.lean`, reused here by name rather than restated:
the total site and each component are small at the site universe, which is what makes abelian
sheaves on them sheafifiable, and restriction to a component is exact by Stacks 04BD (2).

## References

* [Stacks Project, Tag 0DC7](https://stacks.math.columbia.edu/tag/0DC7)
* [Stacks Project, Tag 0D7J](https://stacks.math.columbia.edu/tag/0D7J)
* [Stacks Project, Tag 0754](https://stacks.math.columbia.edu/tag/0754)
* [Stacks Project, Tag 07TF](https://stacks.math.columbia.edu/tag/07TF)
* [Stacks Project, Tag 0D72](https://stacks.math.columbia.edu/tag/0D72)
* [Stacks Project, Tag 0D89](https://stacks.math.columbia.edu/tag/0D89)
* [Stacks Project, Tag 0D9W](https://stacks.math.columbia.edu/tag/0D9W)
* [Stacks Project, Tag 0D9Z](https://stacks.math.columbia.edu/tag/0D9Z)
* [Stacks Project, Tag 0DA2](https://stacks.math.columbia.edu/tag/0DA2)
* [Stacks Project, Tag 0D7V](https://stacks.math.columbia.edu/tag/0D7V)
-/


@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.SimplicialSiteSituation
open scoped ZeroObject

namespace Stacks.Cohomology.CohomologicalDescent

universe u

attribute [local instance] CategoryTheory.SimplicialSiteSituation.hasSheafifyTotalModule
  CategoryTheory.SimplicialSiteSituation.wEqualsLocallyBijectiveTotalModule
  CategoryTheory.SimplicialSiteSituation.hasSheafifyComponentModule
  CategoryTheory.SimplicialSiteSituation.wEqualsLocallyBijectiveComponentModule
  CategoryTheory.SimplicialSiteSituation.preservesFiniteLimits_componentModuleRestriction
  CategoryTheory.SimplicialSiteSituation.preservesFiniteColimits_componentModuleRestriction
  CategoryTheory.SimplicialSiteSituation.preservesZero_componentModuleRestriction

variable (S : CategoryTheory.SimplicialSiteSituation.{u})
  (O : Sheaf S.totalTopology CommRingCat.{u})
  (A : ∀ n : SimplexCategory,
    ObjectProperty (SheafOfModules.{u} (componentRingSheaf S (S.totalRingSheaf O) n)))

/-- **The class `A_total` of Stacks 0DC7.** For a family `A_n` of properties of sheaves of
modules on the simplicial components, the sheaves of `O`-modules on the total site which are
cartesian and whose restriction `F_n = g_n^* F` to the degree-`n` component has the property
`A_n`, for every `n`. -/
def cartesianDegreewiseModules : ObjectProperty (SheafOfModules.{u} (S.totalRingSheaf O)) :=
  fun F ↦ IsCartesianModule S O F ∧
    ∀ n : SimplexCategory, A n ((S.componentModuleRestriction (S.totalRingSheaf O) n).obj F)

/-- `A_total` is a weak Serre subcategory of `Mod(O)`. Let `O` be a sheaf of commutative rings on
the total site of a simplicial-site situation such that the pullback of modules along the
transition morphism of each face map is left exact, and let `A_n` be a weak Serre subcategory of
the category of modules on the degree-`n` component, for every `n`. Then the cartesian
`O`-modules whose restriction to each component lies in the class there form a weak Serre
subcategory of `Mod(O)`. -/
@[stacks 0DC7 "the class A_total of cartesian O-modules whose restriction to each simplicial \
component lies in the prescribed class there is a weak Serre subcategory of Mod(O). Two \
hypotheses are carried: hflat, left exactness of the pullback of modules along the transition \
morphism of each face map, which is the hypothesis in the shape this library's Tag 0D7J (2) \
takes it and is weaker than the source's flatness of the face transitions; and hA, that each A_n \
is a weak Serre subcategory. The family A_n is arbitrary, where the source takes the family \
A_{K_n} = prod_i A_{U_{n,i}} attached to a LocalSerreFamily, i.e. to Tags 0DC2, 0DC3 and 0DC4; \
assembling that particular family needs the module form of Tag 0D89 and is not available. NOT \
covered: the equivalence D_A(O_C) = D_{A_total}(O), the two assertions that La^* and Ra_* \
preserve the classes, and the identification of the two functors of the equivalence -- the \
unbounded engine of Tag 0D7V is stated for a RingedToposSiteHom and the augmentation of a \
hypercovering admits no such presentation. NOT covered either: that a^* induces an equivalence \
A = A_total, whose descent half needs the covering argument on the slices C/U_{n,i}"]
theorem isWeakSerreClass_cartesianDegreewiseModules
    (hflat : ∀ (k : ℕ) (i : Fin (k + 2)),
      PreservesFiniteLimits
        ((S.transitionRingedToposHom O (SimplexCategory.δ i)).toModulesHom.pullbackModules))
    (hA : ∀ n : SimplexCategory, (A n).IsWeakSerreClass) :
    (cartesianDegreewiseModules S O A).IsWeakSerreClass := by
  have hcart := S.isCartesianModule_isWeakSerreClass O hflat
  have := hA
  have hiso : (cartesianDegreewiseModules S O A).IsClosedUnderIsomorphisms :=
    { of_iso := fun e h ↦
        ⟨ObjectProperty.prop_of_iso (P := IsCartesianModule S O) e h.1, fun n ↦
          ((A n).inverseImage _).prop_of_iso e (h.2 n)⟩ }
  have hzero : (cartesianDegreewiseModules S O A).ContainsZero :=
    ⟨0, isZero_zero _,
      ObjectProperty.prop_of_isZero (P := IsCartesianModule S O) (isZero_zero _), fun n ↦
        ((A n).inverseImage _).prop_of_isZero (isZero_zero _)⟩
  have hker : (cartesianDegreewiseModules S O A).IsClosedUnderKernels :=
    { kernels_le := by
        rintro _ ⟨f, k, hk, hf⟩
        exact ⟨ObjectProperty.prop_of_isLimit_kernelFork (P := IsCartesianModule S O) hk hf.1.1
            hf.2.1,
          fun n ↦ (A n).prop_of_isLimit_kernelFork
            (k.mapIsLimit hk (S.componentModuleRestriction (S.totalRingSheaf O) n))
            (hf.1.2 n) (hf.2.2 n)⟩ }
  have hcoker : (cartesianDegreewiseModules S O A).IsClosedUnderCokernels :=
    { cokernels_le := by
        rintro _ ⟨f, k, hk, hf⟩
        exact ⟨ObjectProperty.prop_of_isColimit_cokernelCofork (P := IsCartesianModule S O) hk
            hf.1.1 hf.2.1,
          fun n ↦ (A n).prop_of_isColimit_cokernelCofork
            (k.mapIsColimit hk (S.componentModuleRestriction (S.totalRingSheaf O) n))
            (hf.1.2 n) (hf.2.2 n)⟩ }
  have hext : (cartesianDegreewiseModules S O A).IsClosedUnderExtensions :=
    { prop_X₂_of_shortExact := fun hS h₁ h₃ ↦
        ⟨ObjectProperty.prop_X₂_of_shortExact (P := IsCartesianModule S O) hS h₁.1 h₃.1, fun n ↦
          ((A n).inverseImage _).prop_X₂_of_shortExact hS (h₁.2 n) (h₃.2 n)⟩ }
  exact {}

open Stacks.CategoryTheory.Hypercovering in
/-- `A_total` is a weak Serre subcategory, at the total ringed site of a hypercovering. Let `C` be
a site with equalizers and fibre products, let `O_C` be a sheaf of commutative rings on it and let
`K` be a hypercovering of `C`; let `a : (Sh((C/K)_total), O) ⟶ (Sh(C), O_C)` be the ringed
augmentation of Stacks 0D9W, so that `O = a⁻¹O_C`. For a family `A_n` of weak Serre
subcategories of the categories of modules on the localizations `C/K_n`, the cartesian
`O`-modules whose restriction `F_n` lies in `A_n` for every `n` form a weak Serre subcategory of
`Mod(O)`. -/
@[stacks 0DC7 "the class A_total is a weak Serre subcategory of Mod(O), at the total ringed site \
of a hypercovering with O = a^{-1}O_C, i.e. for the site and structure sheaf of Tag 0D9W. Same \
two hypotheses as the general form: hflat, left exactness of the pullback of modules along the \
transition morphism of each face map, and hA, that each A_n is a weak Serre subcategory; and the \
same restriction, that the family A_n is arbitrary rather than the source's prod_i A_{U_{n,i}}. \
None of the derived assertions of the tag are covered here"]
theorem isWeakSerreClass_cartesianDegreewiseModules_hypercovering {C : Type u} [SmallCategory C]
    [CategoryTheory.Limits.HasEqualizers C] [CategoryTheory.Limits.HasPullbacks C]
    (J : Pretopology C)
    (H : Stacks.CategoryTheory.Hypercovering.HypercoveringOfTerminal.{u, u} J)
    (OC : Sheaf J.toGrothendieck CommRingCat.{u})
    (A : ∀ n : SimplexCategory, ObjectProperty (SheafOfModules.{u}
      (componentRingSheaf (hypercoveringSituation J H)
        ((hypercoveringSituation J H).totalRingSheaf
          (hypercoveringRingedAugmentation J H OC).O) n)))
    (hflat : ∀ (k : ℕ) (i : Fin (k + 2)), PreservesFiniteLimits
      (((hypercoveringSituation J H).transitionRingedToposHom
        (hypercoveringRingedAugmentation J H OC).O
        (SimplexCategory.δ i)).toModulesHom.pullbackModules))
    (hA : ∀ n : SimplexCategory, (A n).IsWeakSerreClass) :
    (cartesianDegreewiseModules (hypercoveringSituation J H)
      (hypercoveringRingedAugmentation J H OC).O A).IsWeakSerreClass :=
  isWeakSerreClass_cartesianDegreewiseModules _ _ _ hflat hA

end Stacks.Cohomology.CohomologicalDescent

end
