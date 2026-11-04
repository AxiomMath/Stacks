module

public import StacksFrontier.AlgebraicGeometry.Duality.ClosedImmersionRightAdjointSheafHomLocallySmall
public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.QcqsCoherator
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekAffineComparison.OpenImmersion
public import StacksCore.Tactic.StacksAttribute

/-!
# The upper shriek of a closed immersion is derived sheaf Hom out of the structure sheaf

Let `S` be a Noetherian scheme and let `i : X ⟶ Y` be a morphism of `FTS S`, the category of
[Stacks, Tag 0F42], whose underlying morphism of schemes is a closed immersion.
[Stacks, Tag 0AA2] asserts `i^!(-) = R𝓗om(𝒪_X, -)`. A closed immersion is proper, so it is its own
compactification, and `i^!` is the right adjoint `a` of `Ri_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)`; the
source proves the tag by citing [Stacks, Tag 0A9X], which identifies `a` with `R𝓗om(𝒪_X, -)` on
`D⁺_QCoh(𝒪_Y)`.

What is needed for an arbitrary object `X` of `FTS S` is the *existence* of `a`. The source
obtains it from [Stacks, Tag 0A9E], by Brown representability on the compactly generated
`D_QCoh(𝒪_X)`, and compact generation ([Stacks, Tag 09IS]) is available in this library only
for quasi-affine schemes. This file produces `a` directly instead, with no generation hypothesis:

  `a = DQ_X ∘ R𝓗om(𝒪_X, -) : D_QCoh(𝒪_Y) ⥤ D(𝒪_Y) ⥤ D(𝒪_X) ⥤ D_QCoh(𝒪_X)`,

the composite of the right adjoint `R𝓗om(𝒪_X, -)` of `Ri_* : D(𝒪_X) ⥤ D(𝒪_Y)`
([Stacks, Tag 0A76]) with the coherator `DQ_X` of [Stacks, Tag 0CR0], the right adjoint of
`D_QCoh(𝒪_X) ⥤ D(𝒪_X)`, which exists for every quasi-compact quasi-separated `X`
(`Stacks.Duality.Coherator.isLeftAdjoint_quasiCoherentι`). Since `Ri_*` of a complex with
quasi-coherent cohomology has quasi-coherent cohomology and `D_QCoh(𝒪_Y)` is a full subcategory,
the composite adjunction restricts.

## Main results

* `Stacks.Duality.LocallySmall.closedImmersionCoheratorAdjunction` — the adjunction
  `Ri_* ⊣ DQ_Z ∘ R𝓗om(𝒪_Z, -)` on the quasi-coherent derived categories, for a closed immersion
  `i : Z ⟶ W` and any coherator `DQ_Z` of `Z`.
* `Stacks.Duality.LocallySmall.isLeftAdjoint_affineHomQuasiCoherentDerivedPushforward` —
  `Ri_* : D_QCoh(𝒪_Z) ⥤ D_QCoh(𝒪_W)` has a right adjoint for a closed immersion with
  quasi-compact quasi-separated source. This is [Stacks, Tag 0A9E] for a closed immersion, with no
  hypothesis on the target.
* `Stacks.Duality.LocallySmall.upperShriek_closedImmersion_of_fts` — **[Stacks, Tag 0AA2]**, which
  is also clause (5) of [Stacks, Tag 0AU3].

## Implementation notes

**The model.** The derived categories are the locally small ones,
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`, as everywhere in
`StacksFrontier/AlgebraicGeometry/Duality/ClosedImmersionTwistedInverseImageLocallySmall.lean`. That
is a modelling choice and not a restriction: `D(𝒪_X)` is the same category up to equivalence at
every model, but `HasDerivedCategory` carries the localized category as data, and at
`CategoryTheory.HasDerivedCategory.standard` — where morphisms live in `Type (u + 1)` — the
coproducts that the coherator and the twisted inverse image are built from are not available.

**What `i^!` is.** The upper shriek `Stacks.Duality.upperShriek` of [Stacks, Tag 0A9Y] is defined
from a compactification; for the proper morphism `i` the source takes `X̄ = X`, which is
`Stacks.Duality.properCompactification`, and then `i^! = j^* ∘ a` with `j = 𝟙_X`. The statement
below covers both readings: the upper shriek at that compactification, and every right adjoint of
`Ri_*` (any two being canonically isomorphic), for which the canonical comparison map
`a(K) ⟶ R𝓗om(𝒪_X, K)` (`Stacks.Duality.LocallySmall.rightAdjointToDerivedSheafHom`) is invertible
on `D⁺_QCoh(𝒪_Y)`. The independence of `f^!` of the compactification is the separate
[Stacks, Tag 0AA0].

## References

* [Stacks Project, Tag 0AA2](https://stacks.math.columbia.edu/tag/0AA2)
* [Stacks Project, Tag 0AU3](https://stacks.math.columbia.edu/tag/0AU3)
* [Stacks Project, Tag 0A9X](https://stacks.math.columbia.edu/tag/0A9X)
* [Stacks Project, Tag 0A76](https://stacks.math.columbia.edu/tag/0A76)
* [Stacks Project, Tag 0CR0](https://stacks.math.columbia.edu/tag/0CR0)
* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
* [Stacks Project, Tag 0A9Y](https://stacks.math.columbia.edu/tag/0A9Y)
* [Stacks Project, Tag 0F42](https://stacks.math.columbia.edu/tag/0F42)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory RingedSpaceModuleAdjunction

universe u

namespace Stacks.Duality.LocallySmall

section ClosedImmersion

variable {Z W : Scheme.{u}} (i : Z ⟶ W) [IsClosedImmersion i]

/-- **The right adjoint of `Ri_*` on the quasi-coherent derived categories, for a closed
immersion.** Let `i : Z ⟶ W` be a closed immersion and let `DQ_Z` be a right adjoint of the
inclusion `D_QCoh(𝒪_Z) ⥤ D(𝒪_Z)`. Then `Ri_* : D_QCoh(𝒪_Z) ⥤ D_QCoh(𝒪_W)` is left adjoint to
`DQ_Z ∘ R𝓗om(𝒪_Z, -)` restricted to `D_QCoh(𝒪_W)`.

The composite `D_QCoh(𝒪_Z) ⥤ D(𝒪_Z) ⥤ D(𝒪_W)` of the inclusion with `Ri_*` is left adjoint to
`R𝓗om(𝒪_Z, -) ⋙ DQ_Z` by composing `ι ⊣ DQ_Z` with [Stacks, Tag 0A76]
(`Stacks.Duality.LocallySmall.derivedModulePushforwardSheafHomExactSupportAdjunction`, with the two
models of `Ri_*` identified by `Stacks.Duality.LocallySmall.closedImmersionPushforwardModelIso`);
that composite is the restricted `Ri_*` followed by the fully faithful inclusion of `D_QCoh(𝒪_W)`,
so `CategoryTheory.Adjunction.restrictFullyFaithful` restricts the adjunction. -/
def closedImmersionCoheratorAdjunction
    (DQ : DerivedCategory Z.Modules ⥤ quasiCoherentDerivedCategory Z)
    (adjZ : Coherator.quasiCoherentι Z ⊣ DQ) :
    affineHomQuasiCoherentDerivedPushforward i ⊣
      Coherator.quasiCoherentι W ⋙ derivedSheafHomExactSupport i ⋙ DQ :=
  Adjunction.restrictFullyFaithful
    ((adjZ.comp (derivedModulePushforwardSheafHomExactSupportAdjunction i)).ofNatIsoLeft
      ((Functor.isoWhiskerLeft (Coherator.quasiCoherentι Z)
          (closedImmersionPushforwardModelIso i)) ≪≫
        ((DerivedCategoryB.derivedCategoryB (A := W.Modules)
          (SheafOfModules.isQuasicoherent W.ringCatSheaf)).liftCompιIso _
            (isQuasicoherent_homology_derivedPushforward_of_isAffineHom i)).symm))
    (Functor.FullyFaithful.id _)
    (DerivedCategoryB.derivedCategoryB (A := W.Modules)
      (SheafOfModules.isQuasicoherent W.ringCatSheaf)).fullyFaithfulι
    (Functor.leftUnitor _) (Functor.rightUnitor _).symm

/-- **[Stacks, Tag 0A9E] for a closed immersion, with no hypothesis on the target.** For a closed
immersion `i : Z ⟶ W` with `Z` quasi-compact and quasi-separated,
`Ri_* : D_QCoh(𝒪_Z) ⥤ D_QCoh(𝒪_W)` has a right adjoint: `DQ_Z ∘ R𝓗om(𝒪_Z, -)`, the coherator
of `Z` existing by [Stacks, Tag 0CR0] (`Stacks.Duality.Coherator.isLeftAdjoint_quasiCoherentι`).
No compact generation of `D_QCoh(𝒪_Z)` is used. -/
instance isLeftAdjoint_affineHomQuasiCoherentDerivedPushforward [CompactSpace Z]
    [QuasiSeparatedSpace Z] : (affineHomQuasiCoherentDerivedPushforward i).IsLeftAdjoint := by
  have := Coherator.isLeftAdjoint_quasiCoherentι Z
  exact (closedImmersionCoheratorAdjunction i _
    (Adjunction.ofIsLeftAdjoint (Coherator.quasiCoherentι Z))).isLeftAdjoint

end ClosedImmersion

/-- **Stacks Project, Tag 0AA2 (Lemma 48.17.4).** In Situation 48.16.1 — `S` a Noetherian scheme
and `FTS S` the schemes separated and of finite type over `S` — let `i : X ⟶ Y` be a morphism of
`FTS S` whose underlying morphism of schemes is a closed immersion. Then
`i^!(-) = R𝓗om(𝒪_X, -)`:

1. `Ri_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` has a right adjoint;
2. the upper shriek `i^! = j^* ∘ a` of [Stacks, Tag 0A9Y] at the compactification `X̄ = X` that a
   proper morphism is (`Stacks.Duality.properCompactification`), with its right adjoint `a`
   *produced* by (1) and its quasi-coherence inputs discharged, agrees with `R𝓗om(𝒪_X, -)` on
   `D⁺_QCoh(𝒪_Y)`;
3. for every right adjoint `a` of `Ri_*` the canonical comparison `a(K) ⟶ R𝓗om(𝒪_X, K)` — the
   mate of the counit of `a` under [Stacks, Tag 0A76] — is an isomorphism for every `K` in
   `D⁺_QCoh(𝒪_Y)`.

The existence (1) is
`Stacks.Duality.LocallySmall.isLeftAdjoint_affineHomQuasiCoherentDerivedPushforward`, which builds
the right adjoint as `DQ_X ∘ R𝓗om(𝒪_X, -)` from the coherator of [Stacks, Tag 0CR0]; `X` is
quasi-compact and quasi-separated, being of finite type over a Noetherian scheme. The
identification (2), (3) is [Stacks, Tag 0A9X] at this model
(`Stacks.Duality.LocallySmall.isIso_rightAdjointToDerivedSheafHom_app`), whose hypotheses —
pseudo-coherence of `i` — hold in Situation 48.16.1. -/
@[stacks 0AA2 "at the locally small derived categories, the model at which the coherator and the \
right adjoint of Ri_* are built; i^! is constructed here",
  stacks 0AU3 "clause (5): for a closed immersion f^! = RHom(O_X, -), at the locally small \
  derived categories"]
theorem upperShriek_closedImmersion_of_fts {S : Scheme.{u}} [IsNoetherian S] {X Y : FTS S}
    (i : X ⟶ Y) [IsClosedImmersion i.left] :
    (affineHomQuasiCoherentDerivedPushforward i.left).IsLeftAdjoint ∧
      IsDerivedSheafHomRightAdjoint i.left
        (upperShriek i (properCompactification i)) ∧
      ∀ (a : quasiCoherentDerivedCategory Y.left ⥤ quasiCoherentDerivedCategory X.left)
        (adj : affineHomQuasiCoherentDerivedPushforward i.left ⊣ a)
        (K : (isBoundedBelowQuasiCoherent Y.left).FullSubcategory),
        IsIso ((rightAdjointToDerivedSheafHom i.left
          (isQuasicoherent_homology_derivedPushforward_of_isAffineHom i.left) a adj).app
            K.obj) := by
  refine ⟨inferInstance, ?_, fun a adj K => isIso_rightAdjointToDerivedSheafHom_app i.left _ a adj
    (FTS.pseudoCoherent_left_of_isClosedImmersion i) K⟩
  exact isDerivedSheafHomRightAdjoint_of_fts_closedImmersion i _
    ((twistedInverseImageAdjunction i.left
        (isQuasicoherent_homology_derivedPushforward_of_isAffineHom i.left)).ofNatIsoRight
      ((Functor.rightUnitor _).symm ≪≫ Functor.isoWhiskerLeft _ (quasiCoherentDerivedPullbackIdIso
        X.left (isQuasicoherent_homology_derivedPullback' (𝟙 X.left))).symm))

/-- **[Stacks, Tag 0AA2], existence form.** In Situation 48.16.1, for `i : X ⟶ Y` a morphism of
`FTS S` whose underlying morphism of schemes is a closed immersion, `Ri_*` has a right adjoint
`i^!`, and `i^!(-) = R𝓗om(𝒪_X, -)` on `D⁺_QCoh(𝒪_Y)`. This is
`Stacks.Duality.LocallySmall.upperShriek_closedImmersion_of_fts`, which says more. -/
theorem exists_isDerivedSheafHomRightAdjoint_of_fts {S : Scheme.{u}} [IsNoetherian S]
    {X Y : FTS S} (i : X ⟶ Y) [IsClosedImmersion i.left] :
    ∃ (a : quasiCoherentDerivedCategory Y.left ⥤ quasiCoherentDerivedCategory X.left)
      (_ : affineHomQuasiCoherentDerivedPushforward i.left ⊣ a),
      IsDerivedSheafHomRightAdjoint i.left a :=
  ⟨_, Adjunction.ofIsLeftAdjoint _, isDerivedSheafHomRightAdjoint_of_fts_closedImmersion i _
    (Adjunction.ofIsLeftAdjoint _)⟩

end Stacks.Duality.LocallySmall

end
