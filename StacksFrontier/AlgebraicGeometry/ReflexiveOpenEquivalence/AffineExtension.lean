module

public import StacksFrontier.AlgebraicGeometry.ReflexiveOpenEquivalence.Extension
public import StacksFrontier.AlgebraicGeometry.FiniteTypeSubmodule.AffineCase
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.QuasiCoherentExtension

/-!
# Extension of a coherent module from an open of an affine scheme

Let `X` be an affine locally Noetherian scheme and let `U ⊆ X` be open.  Every coherent
`𝒪_U`-module is the restriction of a coherent `𝒪_X`-module.  This is part (1) of
[Stacks, Tag 0G41](https://stacks.math.columbia.edu/tag/0G41) in the affine case, which is the
case the proof of [Stacks, Tag 0EBJ](https://stacks.math.columbia.edu/tag/0EBJ) quotes after
reducing to `X` affine.

The source deduces part (1) of Tag 0G41 from two lemmas: Tag 01PE, which writes the given module
on `U` as the restriction of a quasi-coherent module on `X` with no finiteness, and Tag 01PF,
which replaces that module by a quasi-coherent submodule of finite type agreeing with it over
`U`.  Both are formalized — Tag 01PE in general, Tag 01PF in the affine case — so this file is the
composition of the two, followed by Tag 01XZ to turn "quasi-coherent of finite type" back into
"coherent".

The direct-image step of Tag 0EBJ for an affine `X` follows at once, by feeding the extension to
the two statements of
`StacksFrontier/AlgebraicGeometry/ReflexiveOpenEquivalence/Extension.lean`.

## Main results

* `exists_isCoherent_extension_of_isAffine`: **part (1) of Tag 0G41 for an affine locally
  Noetherian scheme**, in the coherent form.
* `isCoherent_and_isReflexive_pushforward_of_isAffine`: **the direct-image step of Tag 0EBJ for
  an affine scheme**, with no hypothesis beyond the depth condition on the complement.

## Implementation notes

Tag 01PE is applied with the structure sheaf as the ambient module and the zero morphism, since
the extension of a *morphism* into a quasi-coherent module specialises to the extension of a
module as soon as any quasi-coherent target is available.  The quasi-compactness that both
Tag 01PE and Tag 01PF require of the open is automatic here: an affine scheme whose ring of
global sections is Noetherian is a Noetherian topological space, so every open is compact.

## References

* [Stacks Project, Tag 01PE](https://stacks.math.columbia.edu/tag/01PE)
* [Stacks Project, Tag 01PF](https://stacks.math.columbia.edu/tag/01PF)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
* [Stacks Project, Tag 0EBJ](https://stacks.math.columbia.edu/tag/0EBJ)
* [Stacks Project, Tag 0G41](https://stacks.math.columbia.edu/tag/0G41)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.ReflexiveModules

/-- **Part (1) of Stacks, Tag 0G41, for an affine locally Noetherian scheme.**  Every coherent
module on an open subscheme of an affine locally Noetherian scheme is the restriction of a
coherent module on the whole scheme.

Tag 01PE gives a quasi-coherent extension `H` with no finiteness condition; Tag 01PF, in the
affine case, replaces `H` by a quasi-coherent submodule of finite type whose inclusion restricts
to an isomorphism over `U`; and Tag 01XZ turns quasi-coherent of finite type into coherent. -/
public theorem exists_isCoherent_extension_of_isAffine {X : Scheme.{u}} [IsAffine X]
    [IsLocallyNoetherian X] (U : X.Opens) (G : U.toScheme.Modules) (hGcoh : G.IsCoherent) :
    ∃ F : X.Modules, F.IsCoherent ∧ Nonempty (F.restrict U.ι ≅ G) := by
  have : IsNoetherianRing Γ(X, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top X⟩
  have : NoetherianSpace X := noetherianSpace_of_isAffine
  have hGq : G.IsQuasicoherent := _root_.isQuasicoherent_of_isCoherent G
  have hGft : _root_.SheafOfModules.IsFiniteType.{u, u, u} G :=
    _root_.SheafOfModules.IsCoherent.isFiniteType
  obtain ⟨H, hH, -, e, -⟩ := AlgebraicGeometry.exists_quasicoherent_extension U.ι
    (_root_.SheafOfModules.unit X.ringCatSheaf) G 0
  have := hH
  have := hGft
  have hft : _root_.SheafOfModules.IsFiniteType.{u, u, u} (H.restrict U.ι) :=
    Stacks.SheafOfModules.isFiniteType_of_iso.{u} e.symm
  obtain ⟨A, hAq, hAft, hAiso⟩ :=
    FiniteTypeSubmodule.exists_finiteTypeQuasicoherentSubobject_isIso_restrict
      H (NoetherianSpace.isCompact U.1) hft
  have := hAq
  have := hAft
  have := hAiso
  exact ⟨(A : X.Modules),
    CoherenceCriteria.isCoherent_of_isQuasicoherent_of_isFiniteType _,
    ⟨asIso ((Scheme.Modules.restrictFunctor U.ι).map A.arrow) ≪≫ e⟩⟩

/-- **The direct-image step of Stacks, Tag 0EBJ, for an affine scheme.**  On an integral affine
locally Noetherian scheme, the direct image of a coherent reflexive module on an open subscheme
whose complement has structure-sheaf depth at least two is again coherent and reflexive.

This is the source's argument after its reduction to the affine case: the extension is
`exists_isCoherent_extension_of_isAffine`, the replacement by the reflexive hull is
`exists_isReflexive_extension_of_isCoherent_extension`, and the conclusion is
`isCoherent_and_isReflexive_pushforward_of_isReflexive_extension`. -/
public theorem isCoherent_and_isReflexive_pushforward_of_isAffine (X : Scheme.{u})
    [AlgebraicGeometry.IsIntegral X] [IsLocallyNoetherian X] [IsAffine X] (U : X.Opens)
    (hdepth : ∀ x : X, x ∉ (U : Set X) →
      (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x))
    (G : U.toScheme.Modules) (hGcoh : G.IsCoherent) (hGrefl : IsReflexive G) :
    ((Scheme.Modules.pushforward U.ι).obj G).IsCoherent ∧
      IsReflexive ((Scheme.Modules.pushforward U.ι).obj G) := by
  obtain ⟨F, hFcoh, ⟨e⟩⟩ := exists_isCoherent_extension_of_isAffine U G hGcoh
  obtain ⟨F', hF'coh, hF'refl, ⟨e'⟩⟩ :=
    exists_isReflexive_extension_of_isCoherent_extension X U G hGrefl F hFcoh e
  exact isCoherent_and_isReflexive_pushforward_of_isReflexive_extension X U hdepth G F'
    hF'coh hF'refl e'

end Stacks.AlgebraicGeometry.ReflexiveModules

end
