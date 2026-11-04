module

public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinChartData
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinDifferentialCompatibility

/-!
# Local cohomology over an open disjoint from its support

Let `T` be a closed subset of a scheme `X` and let `V` be an open subset with `V ∩ T = ∅`. Then
the local cohomology sheaf `i_*ℋ ⁿ_T(ℱ)` has only the zero section over `V`, in every degree and
for every coefficient module.

The reason is that the sheaf is a direct image from `T`: by
`Stacks.Perfect.GysinLocalCohomology.supportCohomologySheafFunctorIso` the degree-`n` cohomology
sheaf of `i_* R𝓗_T(ℱ[0])` is the direct image along the inclusion of `T` of a sheaf on `T`, and
the preimage of `V` in `T` is the empty open, where a sheaf of modules has a single section.

**This is the mirror of the source-side statement** of the Gysin map's uniqueness. There the
source `i_*Ω^p_{Z/S}` is a direct image along `i` and its sections over an open missing the image
vanish, by `AlgebraicGeometry.Scheme.Modules.subsingleton_pushforward_sections_of_disjoint_range`
through `Stacks.Gysin.subsingleton_pushforwardRelativeForms_of_disjoint`. The Gysin map's
*target* is also a direct image, from the closed subset rather than from `Z`, and the same
argument applies to it — which is what lets a statement about the target be glued on the equation
charts augmented by the complement of the closed subset, at every conormal rank including `0`.

Nothing here depends on a closed immersion, on a conormal rank, on the degree, or on the
coefficient module being a sheaf of relative differential forms: the hypotheses are that `T` is
closed and that `V` misses it.

## Main results

* `RingedSpaceModuleAdjunction.subsingleton_sections_bot`: a sheaf of modules on a ringed space
  has a single section over the empty open. The ringed space is needed, rather than a scheme, for
  the closed subset carrying the local cohomology, which is not a scheme; the scheme-level
  statement is `Stacks.Tag0B5PClopenLift.subsingleton_sections_bot`.
* `RingedSpaceModuleAdjunction.subsingleton_modulePushforward_sections_of_opensMap_eq_bot`: a
  direct image of sheaves of modules along a morphism of ringed spaces has a single section over
  an open whose preimage is empty.
* `Stacks.Perfect.GysinLocalCohomology.subsingleton_supportCohomologySheaf_sections_of_disjoint`:
  **the statement of this file** — `i_*ℋ ⁿ_T(ℱ)` has a single section over an open disjoint
  from `T`.
* `Stacks.Gysin.subsingleton_gysinTarget_sections_of_disjoint`: the instance the Gysin map's
  target is consumed at.

## References

* [Stacks Project, Tag 0G78](https://stacks.math.columbia.edu/tag/0G78)
* [Stacks Project, Tag 0G86](https://stacks.math.columbia.edu/tag/0G86)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Hom
open Stacks.Cohomology.SupportedComplexes
open Stacks.Perfect.SupportedFraction

universe u

namespace RingedSpaceModuleAdjunction

/-- **A sheaf of modules on a ringed space has a single section over the empty open.**  Its
ring of scalars over the empty open is the zero ring, by the sheaf condition of the structure
sheaf against the empty cover, so `1 = 0` acts on every section. -/
theorem subsingleton_sections_bot (Y : RingedSpace.{u, u})
    (M : _root_.SheafOfModules.{u} (structureSheafRing Y)) :
    Subsingleton (ToType (M.val.obj (op (⊥ : Opens Y.carrier)))) := by
  have : Subsingleton (ToType ((structureSheafRing Y).obj.obj (op (⊥ : Opens Y.carrier)))) :=
    CommRingCat.subsingleton_of_isTerminal (TopCat.Sheaf.isTerminalOfEmpty Y.sheaf)
  exact Module.subsingleton (ToType ((structureSheafRing Y).obj.obj (op (⊥ : Opens Y.carrier)))) _

/-- **A direct image of sheaves of modules has a single section over an open whose preimage is
empty.**  Its sections over the open are by definition the sections of the module over the
preimage. -/
theorem subsingleton_modulePushforward_sections_of_opensMap_eq_bot {Y Y' : RingedSpace.{u, u}}
    (f : Y ⟶ Y') (M : _root_.SheafOfModules.{u} (structureSheafRing Y))
    (V : Opens Y'.carrier) (hV : (opensMap f).obj V = ⊥) :
    Subsingleton (ToType (((modulePushforward f).obj M).val.obj (op V))) := by
  have h : Subsingleton (ToType (M.val.obj (op ((opensMap f).obj V)))) := by
    rw [hV]
    exact subsingleton_sections_bot Y M
  exact h

end RingedSpaceModuleAdjunction

open RingedSpaceModuleAdjunction

namespace Stacks.Cohomology.SupportedComplexes

/-- **The preimage in a closed subset of an open disjoint from it is the empty open.** -/
theorem opensMap_closedSubsetInclusion_eq_bot {X : Scheme.{u}} (T : Set X) (V : X.Opens)
    (hV : (V : Set X) ∩ T = ∅) :
    (opensMap (closedSubsetInclusion X.toRingedSpace T)).obj V = ⊥ := by
  ext x
  refine ⟨fun hx => ?_, fun hx => hx.elim⟩
  exact (hV.subset ⟨hx, x.2⟩).elim

end Stacks.Cohomology.SupportedComplexes

namespace Stacks.Perfect.GysinLocalCohomology

attribute [local instance 10000] HasDerivedCategory.standard

variable {X : Scheme.{u}}

/-- **Local cohomology supported on a closed subset has a single section over an open disjoint
from that subset**, in every degree and for every coefficient module.

The sheaf is a direct image from `T`, by `supportCohomologySheafFunctorIso`, and the preimage of
the open in `T` is empty by
`Stacks.Cohomology.SupportedComplexes.opensMap_closedSubsetInclusion_eq_bot`.  The only
hypotheses are that `T` is closed and that the open misses it. -/
theorem subsingleton_supportCohomologySheaf_sections_of_disjoint {T : Set X} (hT : IsClosed T)
    (n : ℤ) (F : X.Modules) (V : X.Opens) (hV : (V : Set X) ∩ T = ∅) :
    Subsingleton Γ(supportCohomologySheaf hT F n, V) := by
  have htarget : Subsingleton Γ((localCohomologyPushforwardFunctor hT n).obj F, V) :=
    subsingleton_modulePushforward_sections_of_opensMap_eq_bot _ _ V
      (opensMap_closedSubsetInclusion_eq_bot T V hV)
  refine ⟨fun a b => ?_⟩
  have e := (supportCohomologySheafFunctorIso hT n).app F
  have hround : ∀ x : Γ(supportCohomologySheaf hT F n, V), e.inv.app V (e.hom.app V x) = x :=
    fun x => congrArg
      (fun φ : supportCohomologySheaf hT F n ⟶ supportCohomologySheaf hT F n => φ.app V x)
      e.hom_inv_id
  rw [← hround a, ← hround b, htarget.elim (e.hom.app V a) (e.hom.app V b)]

end Stacks.Perfect.GysinLocalCohomology

namespace Stacks.Gysin

attribute [local instance 10000] HasDerivedCategory.standard

/-- **The target of the Gysin map of [Stacks, Tag 0G86] has a single section over an open missing
the image of the closed immersion**, at every rank and in every degree.  It is the instance of
`Stacks.Perfect.GysinLocalCohomology.subsingleton_supportCohomologySheaf_sections_of_disjoint`
at the closed subset `Set.range i.base`, and the mirror of
`Stacks.Gysin.subsingleton_pushforwardRelativeForms_of_disjoint` on the source. -/
theorem subsingleton_gysinTarget_sections_of_disjoint {Z X S : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (π : X ⟶ S) (c p : ℕ) (V : X.Opens)
    (hV : (V : Set X) ∩ Set.range i.base = ∅) :
    Subsingleton Γ(gysinTarget i π c p, V) :=
  Stacks.Perfect.GysinLocalCohomology.subsingleton_supportCohomologySheaf_sections_of_disjoint
    (isClosed_range_base i) (c : ℤ) (relativeDifferentialForms π ((p : ℤ) + (c : ℤ))) V hV

end Stacks.Gysin

end
