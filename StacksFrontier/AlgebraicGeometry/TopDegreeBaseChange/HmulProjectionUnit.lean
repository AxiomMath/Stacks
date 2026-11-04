module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.AffineTildeCounit
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.BaseChangeSectionsBijection
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.HmulProjectionSection

/-!
# Multiplication crosses the tilde comparison of a direct image of a structure sheaf

`Stacks.AlgebraicGeometry.TopDegreeBaseChange.pushforwardUnitIsoAffineTilde` identifies the
direct image `q_* 𝒪_P` along an affine morphism `q : P ⟶ Z` to an affine scheme with the module
associated to its global sections. The computation of the right-hand end of the comparison map of
[Stacks, Tag 0EX3] (c) crosses that identification, and needs multiplication by a global function
on `P` to cross with it.

The crossing itself is free: the identification is natural in the module
(`Stacks.Coherent.affineTildeObjSectionsIso_hom_naturality`), and multiplication by a function on
`P`, pushed forward, is a morphism like any other. What is **not** free, and is what this file
supplies, is the identification of the global sections of that pushed-forward multiplication with
multiplication in the ring: the direct image along `q` of multiplication by `a` on `𝒪_P` has
global sections `x ↦ a * x` on `Γ(P, ⊤)`, read as a module over `Γ(Z, ⊤)` through `q^♯`.

## Main results

* `…TopDegreeBaseChange.evaluation_map_pushforward_sectionScalar`: **the global sections of the
  direct image of multiplication by a global function are multiplication by that function**, in
  the spelling `…TopDegreeBaseChange.mulLeftRestrictScalars` that the Eilenberg-Watts
  presentation of conclusion (b) consumes.
* `…TopDegreeBaseChange.mulLeftRestrictScalars_comp_pushforwardUnitIsoAffineTilde`: **the tilde
  comparison of `q_* 𝒪_P` intertwines multiplication by `a` on the module of sections with
  multiplication by `a` on `q_* 𝒪_P`.**

## Implementation notes

*Why the sections statement is proved on an element.*
`AlgebraicGeometry.Scheme.Modules.pushforward` evaluates at the top open of `Z` to the sections
over `q⁻¹(⊤)`, which is `⊤`, and `AlgebraicGeometry.IntegralTransformQcoh.sectionScalar` multiplies
there by the restriction of `a` along the inclusion `q⁻¹(⊤) ≤ ⊤`. That inclusion is the identity,
but only after `CategoryTheory.Functor.map_id`; there is nothing else in the proof. The opens
category is thin, so the inclusion is identified with the identity by `Subsingleton.elim`, as in
the `sectionScalar` computation at the top open.

*The statement is at two definitionally equal spellings of one object.* The source and target of
the left-hand side are written with `SheafOfModules.evaluation`, those of the right-hand side
with `ModuleCat.restrictScalars`; they agree definitionally, which is what lets
`…TopDegreeBaseChange.sectionsIsoPushforwardUnitSections` be stated at the second and consumed at
the first.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry.IntegralTransformQcoh
open Stacks.Cohomology.AffineBase
open scoped ChangeOfRings

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

attribute [local instance 100000] HasDerivedCategory.standard

/-- **The global sections of the direct image of multiplication by a global function are
multiplication by that function.** For a morphism of schemes `q : P ⟶ Z` and a global function
`a` on `P`, the value at the top open of `Z` of the direct image along `q` of multiplication by
`a` on `𝒪_P` is multiplication by `a` on `Γ(P, ⊤)`, read as a `Γ(Z, ⊤)`-module through `q^♯`.

On an element both sides are `a * x`: the left-hand side multiplies by the restriction of `a`
along `q⁻¹(⊤) ≤ ⊤`, and that inclusion is the identity. -/
theorem evaluation_map_pushforward_sectionScalar {P Z : Scheme.{u}} (q : P ⟶ Z)
    (a : Γ(P, ⊤)) :
    (_root_.SheafOfModules.evaluation Z.ringCatSheaf (op ⊤)).map
        ((Scheme.Modules.pushforward q).map (sectionScalar P a (Scheme.unitModule P))) =
      mulLeftRestrictScalars q.appTop.hom a := by
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  have key : ∀ y : Γ(P, ⊤),
      (ConcreteCategory.hom (P.presheaf.map (Opens.leTop (⊤ : P.Opens)).op) a : Γ(P, ⊤)) • y =
        a * y := by
    intro y
    rw [show ((⊤ : P.Opens)).leTop = 𝟙 (⊤ : P.Opens) from rfl, op_id, P.presheaf.map_id]
    rfl
  exact key x

/-- **The tilde comparison of a direct image of a structure sheaf intertwines multiplication.**
For an affine morphism `q : P ⟶ Z` to an affine scheme and a global function `a` on `P`,
`…TopDegreeBaseChange.pushforwardUnitIsoAffineTilde` carries multiplication by `a` on the module
of global sections of `q_* 𝒪_P` to multiplication by `a` on `q_* 𝒪_P`.

This is the naturality of `Stacks.Coherent.affineTildeObjSectionsIso` at the endomorphism
`q_*`(multiplication by `a`), whose global sections are computed by
`evaluation_map_pushforward_sectionScalar`. -/
theorem mulLeftRestrictScalars_comp_pushforwardUnitIsoAffineTilde {P Z : Scheme.{u}}
    [IsAffine Z] (q : P ⟶ Z) [IsAffineHom q] (a : Γ(P, ⊤)) :
    (Stacks.Coherent.affineTilde Z).map (mulLeftRestrictScalars q.appTop.hom a) ≫
        (pushforwardUnitIsoAffineTilde q).hom =
      (pushforwardUnitIsoAffineTilde q).hom ≫
        (Scheme.Modules.pushforward q).map (sectionScalar P a (Scheme.unitModule P)) := by
  refine Eq.trans ?_ (Stacks.Coherent.affineTildeObjSectionsIso_hom_naturality Z
    (Stacks.Modules.isQuasicoherent_pushforward_of_isAffineHom q _ inferInstance)
    (Stacks.Modules.isQuasicoherent_pushforward_of_isAffineHom q _ inferInstance)
    ((Scheme.Modules.pushforward q).map (sectionScalar P a (Scheme.unitModule P))))
  exact congrArg
    (fun z => (Stacks.Coherent.affineTilde Z).map z ≫ (pushforwardUnitIsoAffineTilde q).hom)
    (evaluation_map_pushforward_sectionScalar q a).symm

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
