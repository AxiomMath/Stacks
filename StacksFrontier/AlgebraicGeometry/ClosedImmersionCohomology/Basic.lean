module

public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.AffineBase
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionCohomology.DerivedCollapse
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.DerivedPushforwardRelative
public import StacksFrontier.Topology.Sheaves.Cohomology.CechAcyclicity.PushforwardOfAnInjective
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.SectionsOverAnOpen

/-!
# Cohomology does not change along a closed immersion

For a closed immersion of schemes `i : Z ⟶ X` and a sheaf of modules `G` on `Z`, the cohomology
of `i_* G` on `X` is the cohomology of `G` on `Z`:

`Rⁿ Γ(Z, G) ≅ Rⁿ Γ(X, i_* G)`.

The two sides are modules over *different* rings — `Γ(Z, ⊤)` and `Γ(X, ⊤)` — so the comparison
is stated after restriction of scalars along `i.appTop : Γ(X, ⊤) ⟶ Γ(Z, ⊤)`, exactly as the
underived identification `Stacks.Cohomology.AffineBase.sectionsRestrictionIsoTop` is. There is no
isomorphism between the two sides as written without that decoration, because there is no
functor between the two categories without it.

## Main results

* `Stacks.Cohomology.ClosedImmersion.rightAcyclic_moduleGlobalSections_pushforward_injective`:
  global sections on `X` are acyclic on the pushforward of an injective module. True for an
  arbitrary morphism of schemes; this is [Stacks, Tag 01EX] part (2) at the whole space.
* `Stacks.Cohomology.ClosedImmersion.closedImmersionCohomologyIso`: the natural isomorphism
  `Rⁿ Γ_Z ⋙ restrictScalars i.appTop ≅ i_* ⋙ Rⁿ Γ_X`, for `i` a closed immersion, every `n`,
  and **every** sheaf of modules on `Z` — no quasi-coherence, no properness, no Noetherian
  hypothesis.
* `Stacks.Cohomology.ClosedImmersion.cohomologyObjIsoPushforward`: the same at a fixed module,
  in the object spelling a consumer uses.

## Implementation notes

**What is special about a closed immersion, and what is not.** The route is the collapse of the
derived functor of the composite `Γ_X ∘ i_* = Γ_Z` (`rightDerivedCompIsoOfAcyclic`), which needs
two things of `i_*`: that it carry injectives to `Γ_X`-acyclic objects, and that it be exact.
The *first* is not special at all — [Stacks, Tag 01EX] part (2) gives it for an arbitrary
morphism of ringed spaces, which is why the Leray spectral sequence of a general morphism has
`Rᵖ Γ ∘ Rᑫ f_*` as its page. The *second* is what closedness buys, and it is proved as
`AlgebraicGeometry.Scheme.Modules.preservesFiniteColimits_pushforward_of_isClosedImmersion`:
once `i_*` is exact it is its own derived functor, so the composite collapses degreewise instead
of only to a spectral sequence.

**`i_*` does not preserve injectives, so the usual splitting lemma does not apply.**
`Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso` would give the same conclusion
from `(i_*).PreservesInjectiveObjects`, and that hypothesis is false here: for `Z = Spec k`
closed in `X = Spec k[x]/(x²)`, `i_*` is restriction of scalars along `k[x]/(x²) ⟶ k`, whose left
adjoint `− ⊗ k` is not exact, and indeed `k` is not injective over the self-injective ring
`k[x]/(x²)`. Acyclicity of the values is the weaker hypothesis that survives, which is why
`rightDerivedCompIsoOfAcyclic` is stated with it.

**Spelling.** Everything here is in Mathlib's `ℕ`-indexed `Functor.rightDerived` of module-valued
global sections. It is not the `ℤ`-indexed `rightDerivedPlus` and not `Hgroup`; the crossings to
those are `Stacks.DerivedIndexing.rightDerivedIso` and
`Stacks.Cohomology.AffineBase.rightAcyclic_moduleGlobalSections`'s route respectively, and
neither is performed here.

## References

* [Stacks Project, Tag 01EX](https://stacks.math.columbia.edu/tag/01EX)
* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped AlgebraicGeometry

namespace Stacks.Cohomology.ClosedImmersion

open Stacks.Cohomology.AffineBase

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {Z X : AlgebraicGeometry.Scheme.{u}} (i : Z ⟶ X)

/-- **[Stacks, Tag 01EX] part (2) at the whole space.** Global sections on the target are
acyclic on the pushforward of an injective sheaf of modules. No hypothesis on `i`: this is the
acyclicity that makes the Leray comparison of an arbitrary morphism available. -/
theorem rightAcyclic_moduleGlobalSections_pushforward_injective
    (I : Z.Modules) (hI : Injective I) :
    (moduleGlobalSections X).rightAcyclic
      ((AlgebraicGeometry.Scheme.Modules.pushforward i).obj I) :=
  @Stacks.Cohomology.PushforwardAcyclic.pushforward_injective_rightAcyclic _ _
    (asRingedSpaceHom i) I hI ⊤

/-- **Cohomology does not change along a closed immersion.** For a closed immersion
`i : Z ⟶ X`, the `n`-th cohomology of a sheaf of modules on `Z`, viewed as a `Γ(X, ⊤)`-module
along `i.appTop`, is the `n`-th cohomology on `X` of its pushforward. Naturally in the module,
and for every sheaf of modules on `Z`. -/
noncomputable def closedImmersionCohomologyIso
    [AlgebraicGeometry.IsClosedImmersion i] (n : ℕ) :
    (moduleGlobalSections Z).rightDerived n ⋙ ModuleCat.restrictScalars i.appTop.hom ≅
      AlgebraicGeometry.Scheme.Modules.pushforward i ⋙ (moduleGlobalSections X).rightDerived n :=
  let R := ModuleCat.restrictScalars.{u} i.appTop.hom
  have _ : R.Additive := ⟨by intros; rfl⟩
  have _ : PreservesFiniteLimits R := ⟨fun _ _ _ => ⟨fun {_} => inferInstance⟩⟩
  have _ : PreservesFiniteColimits R := ⟨fun _ _ _ => ⟨fun {_} => inferInstance⟩⟩
  have _ : R.PreservesHomology := Functor.preservesHomologyOfExact R
  Stacks.Cohomology.ModuleComparison.rightDerivedCompIso (moduleGlobalSections Z) R
      (AlgebraicGeometry.Scheme.Modules.pushforward i ⋙ moduleGlobalSections X)
      (sectionsRestrictionIsoTop i) n ≪≫
    Stacks.Cohomology.AcyclicCollapse.rightDerivedCompIsoOfAcyclic
      (AlgebraicGeometry.Scheme.Modules.pushforward i) (moduleGlobalSections X)
      (rightAcyclic_moduleGlobalSections_pushforward_injective i) n

/-- **Cohomology does not change along a closed immersion**, at a fixed sheaf of modules: the
`n`-th cohomology on `X` of `i_* G` is the `n`-th cohomology of `G` on `Z` with scalars
restricted along `i.appTop`. -/
noncomputable def cohomologyObjIsoPushforward
    [AlgebraicGeometry.IsClosedImmersion i] (G : Z.Modules) (n : ℕ) :
    ((moduleGlobalSections X).rightDerived n).obj
        ((AlgebraicGeometry.Scheme.Modules.pushforward i).obj G) ≅
      (ModuleCat.restrictScalars i.appTop.hom).obj
        (((moduleGlobalSections Z).rightDerived n).obj G) :=
  ((closedImmersionCohomologyIso i n).app G).symm

end Stacks.Cohomology.ClosedImmersion

end
