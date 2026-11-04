module

public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiSeparated.LocalizedRestriction
public import StacksFrontier.AlgebraicGeometry.TorsionQuasicoherent.Local
public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksCore.Tactic.StacksAttribute

/-!
# The direct image along the inclusion of an open subscheme

The direct image of a quasi-coherent module along a quasi-compact quasi-separated morphism is
quasi-coherent — [Stacks, Tag 01LC], proved as
`AlgebraicGeometry.pushforward_isQuasicoherent`.  An open immersion is never affine in general,
so the direct image along an affine morphism ([Stacks, Tag 02KG],
`Stacks.AlgebraicGeometry.AffinePushforward.pushforward_isQuasicoherent_of_isAffineHom`) does not
cover the inclusion of an open subscheme.  This file supplies what that case needs: the
inclusion of an open subscheme of a locally Noetherian scheme is quasi-compact, because an
affine open of such a scheme is a Noetherian space and every subset of a Noetherian space is
quasi-compact.

## Main results

* `Stacks.AlgebraicGeometry.QcohPushforwardOpen.isLocalizedModule_restrictₗ_of_eq`: the module
  half of [Stacks, Tag 01P7] with the principal open supplied as a variable together with an
  equation.
* `Stacks.AlgebraicGeometry.QcohPushforwardOpen.quasiCompact_ι_of_isLocallyNoetherian` — the
  inclusion of an open subscheme of a locally Noetherian scheme is quasi-compact.  Together with
  Mathlib's `IsSeparated`-of-a-monomorphism instance this makes [Stacks, Tag 01LC] apply to
  `U.ι` on a locally Noetherian scheme.
* `Stacks.AlgebraicGeometry.QcohPushforwardOpen.isQuasicoherent_pushforward_pullback_ι` — the
  resulting statement for the direct image of the restriction of a quasi-coherent module to an
  open subscheme.

## Implementation notes

`isLocalizedModule_restrictₗ_of_eq` takes the principal open as a variable together with an
equation so that it can be used at an open which is *equal* to `X.basicOpen g` but not
syntactically so: `Γ(F, ·)` of the two is the same type only after rewriting, and the section
types appear in the module instances, so the rewrite has to happen before any instance is fixed.

## References

* [Stacks Project, Tag 01LC](https://stacks.math.columbia.edu/tag/01LC)
* [Stacks Project, Tag 01P7](https://stacks.math.columbia.edu/tag/01P7)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry
open Stacks.AlgebraicGeometry.QuasicoherentBaseChange

universe u

namespace Stacks.AlgebraicGeometry.QcohPushforwardOpen

/-! ### The localization statement at an open given by an equation -/

/-- **[Stacks, Tag 01P7] for quasi-coherent modules, with the principal open given by an
equation.**  On a quasi-compact quasi-separated open `W` of a scheme, restriction of sections of
a quasi-coherent module to any open `V` which *equals* the principal open of `g : Γ(X, W)`
exhibits `Γ(F, V)` as the localization of `Γ(F, W)` away from `g`. -/
@[ega "I 9.6.2" "Γ(D(f)"]
theorem isLocalizedModule_restrictₗ_of_eq {X : Scheme.{u}} (F : X.Modules) [F.IsQuasicoherent]
    {W : X.Opens} (hWc : IsCompact W.1) (hWs : IsQuasiSeparated W.1) (g : Γ(X, W))
    {V : X.Opens} (hV : V = X.basicOpen g) (hVW : V ≤ W) :
    let _ := moduleOfLE F hVW
    IsLocalizedModule.Away g (restrictₗ F hVW) := by
  subst hV
  exact isLocalizedModule_restriction_basicOpen_of_qcqs F hWc hWs g

/-! ### The case of an open subscheme -/

/-- The inclusion of an open subscheme of a locally Noetherian scheme is quasi-compact.  An
affine open `V` of such a scheme is a Noetherian space, so every subset of `V` — in particular
`U ∩ V` — is quasi-compact. -/
@[ega "I 6.1.2" "more general", ega "I 6.6.4" "(i), special case"]
instance quasiCompact_ι_of_isLocallyNoetherian {X : Scheme.{u}} [IsLocallyNoetherian X]
    (U : X.Opens) : QuasiCompact U.ι := by
  rw [quasiCompact_iff_forall_isAffineOpen]
  intro V hV
  have hNR : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  have hN : NoetherianSpace (V : Set X) := noetherianSpace_of_isAffineOpen V hV
  have hcap : IsCompact ((V : Set X) ∩ (U : Set X)) := by
    rw [← Subtype.image_preimage_coe (V : Set X) (U : Set X)]
    exact (NoetherianSpace.isCompact (α := ((V : Set X) : Type u)) _).image continuous_subtype_val
  have hemb : Topology.IsOpenEmbedding U.ι.base := U.isOpenEmbedding
  rw [show ((U.ι ⁻¹ᵁ V : U.toScheme.Opens) : Set U.toScheme)
      = U.ι.base ⁻¹' (V : Set X) from rfl,
    hemb.isEmbedding.isCompact_iff, Set.image_preimage_eq_inter_range]
  simpa [U.range_ι, Set.inter_comm] using hcap

/-- The direct image, along the inclusion of an open subscheme of a locally Noetherian scheme, of
the restriction of a quasi-coherent module is quasi-coherent. -/
theorem isQuasicoherent_pushforward_pullback_ι {X : Scheme.{u}} [IsLocallyNoetherian X]
    (U : X.Opens) (F : X.Modules) [F.IsQuasicoherent] :
    ((Scheme.Modules.pushforward U.ι).obj
      ((Scheme.Modules.pullback U.ι).obj F)).IsQuasicoherent := by
  have hpull : ((Scheme.Modules.pullback U.ι).obj F).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (U : Scheme).ringCatSheaf).prop_of_iso
      ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app F) inferInstance
  exact AlgebraicGeometry.pushforward_isQuasicoherent U.ι
    ((Scheme.Modules.pullback U.ι).obj F)

end Stacks.AlgebraicGeometry.QcohPushforwardOpen

end
