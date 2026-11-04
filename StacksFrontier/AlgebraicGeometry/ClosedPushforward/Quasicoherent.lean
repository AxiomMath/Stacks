module

public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.DerivedPushforwardComparison
public import StacksFrontier.AlgebraicGeometry.ClosedPushforward.Basic
public import StacksFrontier.AlgebraicGeometry.CohomologyAffineReduction.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.AffineBaseChange
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentPullbackScheme
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.WeakSerre.DerivedComparison
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Direct image along a closed immersion, on quasi-coherent modules

Let `i : Z ⟶ X` be a closed immersion of schemes and let `ℐ = ker(i^♯) ⊆ 𝒪_X` be the
quasi-coherent sheaf of ideals cutting out `Z`. Direct image carries quasi-coherent
`𝒪_Z`-modules to quasi-coherent `𝒪_X`-modules, because a closed immersion is an affine
morphism, and the resulting functor

  `i_* : QCoh(𝒪_Z) ⟶ QCoh(𝒪_X)`

is exact and fully faithful, with essential image the quasi-coherent `𝒪_X`-modules annihilated
by `ℐ`.

## Main results

* `Stacks.ClosedImmersion.pushforwardQcoh_exact`: exactness.
* `Stacks.ClosedImmersion.fullyFaithfulPushforwardQcoh`, with
  `Stacks.ClosedImmersion.pushforwardQcoh_full` and
  `Stacks.ClosedImmersion.pushforwardQcoh_faithful`: full faithfulness.
* `Stacks.ClosedImmersion.pushforwardQcoh_essImage_iff`: the essential image consists of the
  quasi-coherent modules annihilated section by section by the kernel of the comorphism.

## Implementation notes

The functor is `Stacks.Modules.pushforwardQcoh i`, the lift of `Scheme.Modules.pushforward i`
to the full subcategories of quasi-coherent modules along the affine-morphism quasi-coherence
statement; a closed immersion is an affine morphism, so no hypothesis beyond
`IsClosedImmersion i` is needed.

All three clauses are deduced from the corresponding statements for *all* modules, which is the
generality of the ringed-space result on direct image along a closed quotient morphism. The
bridge is that `Stacks.Modules.pushforwardQcoh i ⋙ ι = ι ⋙ Scheme.Modules.pushforward i` holds
by definition, together with the inclusion `ι` of quasi-coherent modules being exact (quasi-
coherence is a weak Serre subcategory) and fully faithful, hence reflecting finite limits and
colimits.

For the essential image the module obtained at the level of all modules has to be seen to be
quasi-coherent. Rather than argue about an arbitrary preimage, the pullback `i^*𝒢` is used: the
unit `𝒢 ⟶ i_* i^* 𝒢` of the pullback–pushforward adjunction is an isomorphism as soon as the
kernel of the comorphism annihilates `𝒢`, and a pullback of a quasi-coherent module is
quasi-coherent.

Right exactness of `Scheme.Modules.pushforward i` is recorded here as an instance; what the
tree already had was the ringed-space form, for the morphism of ringed spaces underlying `i`,
and the two functors are equal by definition.

## References

* [Stacks Project, Tag 01QY](https://stacks.math.columbia.edu/tag/01QY)
* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.ClosedImmersion

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [AlgebraicGeometry.IsClosedImmersion i]

/-- Direct image of quasi-coherent modules along a closed immersion is left exact. -/
instance preservesFiniteLimits_pushforwardQcoh :
    PreservesFiniteLimits (Stacks.Modules.pushforwardQcoh i) := by
  have : PreservesFiniteLimits (Stacks.Modules.pushforwardQcoh i ⋙
      (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι) :=
    show PreservesFiniteLimits ((SheafOfModules.isQuasicoherent Z.ringCatSheaf).ι ⋙
      Scheme.Modules.pushforward i) from @comp_preservesFiniteLimits _ _ _ _ _ _ _ _
        (Stacks.AlgebraicGeometry.QuasicoherentDerived.isQuasicoherent_ι_preservesFiniteLimits Z)
        (Stacks.SchemeCohomology.pushforward_preservesFiniteLimits i)
  exact preservesFiniteLimits_of_reflects_of_preserves _
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι

/-- Direct image of quasi-coherent modules along a closed immersion is right exact. -/
instance preservesFiniteColimits_pushforwardQcoh :
    PreservesFiniteColimits (Stacks.Modules.pushforwardQcoh i) := by
  have hι : PreservesFiniteColimits (SheafOfModules.isQuasicoherent Z.ringCatSheaf).ι :=
    Stacks.AlgebraicGeometry.QuasicoherentDerived.isQuasicoherent_ι_preservesFiniteColimits Z
  have hpush : PreservesFiniteColimits (Scheme.Modules.pushforward i) := inferInstance
  have hcomp : PreservesFiniteColimits (Stacks.Modules.pushforwardQcoh i ⋙
      (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι) :=
    show PreservesFiniteColimits ((SheafOfModules.isQuasicoherent Z.ringCatSheaf).ι ⋙
      Scheme.Modules.pushforward i) from @comp_preservesFiniteColimits _ _ _ _ _ _ _ _ hι hpush
  exact preservesFiniteColimits_of_reflects_of_preserves _
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι

/-- **[Stacks, Tag 01QY], exactness.** Direct image along a closed immersion is an exact functor
on quasi-coherent modules. -/
@[stacks 01QY "exactness", ega "I 1.6.4" "closed immersion"]
theorem pushforwardQcoh_exact :
    exactFunctor (SheafOfModules.isQuasicoherent Z.ringCatSheaf).FullSubcategory
      (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory
      (Stacks.Modules.pushforwardQcoh i) :=
  (exactFunctor_iff _).mpr ⟨inferInstance, inferInstance⟩

/-- **[Stacks, Tag 01QY], full faithfulness.** Direct image along a closed immersion is fully
faithful on quasi-coherent modules: it is fully faithful on all modules, and the inclusion of
the quasi-coherent modules is faithful. -/
@[stacks 01QY "full faithfulness"]
def fullyFaithfulPushforwardQcoh : (Stacks.Modules.pushforwardQcoh i).FullyFaithful :=
  Functor.FullyFaithful.ofCompFaithful
    (G := (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι)
    (show (Stacks.Modules.pushforwardQcoh i ⋙
        (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι).FullyFaithful from
      (Functor.FullyFaithful.ofFullyFaithful
        (SheafOfModules.isQuasicoherent Z.ringCatSheaf).ι).comp (fullyFaithfulPushforward i))

/-- **[Stacks, Tag 01QY], fullness.** Direct image along a closed immersion is full on
quasi-coherent modules. -/
@[stacks 01QY "fullness"]
instance pushforwardQcoh_full : (Stacks.Modules.pushforwardQcoh i).Full :=
  (fullyFaithfulPushforwardQcoh i).full

/-- **[Stacks, Tag 01QY], faithfulness.** Direct image along a closed immersion is faithful on
quasi-coherent modules. -/
@[stacks 01QY "faithfulness"]
instance pushforwardQcoh_faithful : (Stacks.Modules.pushforwardQcoh i).Faithful :=
  (fullyFaithfulPushforwardQcoh i).faithful

/-- **[Stacks, Tag 01QY], the essential image.** A quasi-coherent `𝒪_X`-module is a direct image
of a quasi-coherent `𝒪_Z`-module exactly when the kernel of the comorphism of `i` annihilates it
section by section, that is, when the ideal cutting out `Z` kills it. -/
@[stacks 01QY "essential image"]
theorem pushforwardQcoh_essImage_iff (G : X.Modules) (hG : G.IsQuasicoherent) :
    (Stacks.Modules.pushforwardQcoh i).essImage ⟨G, hG⟩ ↔
      ∀ (U : X.Opens) (a : Γ(X, U)), (i.app U).hom a = 0 → ∀ m : Γ(G, U), a • m = 0 := by
  constructor
  · rintro ⟨M, ⟨e⟩⟩
    exact (pushforward_essImage_iff i G).mp
      ⟨M.obj, ⟨(SheafOfModules.isQuasicoherent X.ringCatSheaf).ι.mapIso e⟩⟩
  · intro h
    have hiso := isIso_unit_app_of_smul_eq_zero i G h
    exact ⟨⟨(Scheme.Modules.pullback i).obj G, Stacks.Modules.isQuasicoherent_pullback i G hG⟩,
      ⟨(SheafOfModules.isQuasicoherent X.ringCatSheaf).ι.preimageIso
        (asIso ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app G)).symm⟩⟩

end Stacks.ClosedImmersion

end
