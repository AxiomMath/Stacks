module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdealBijection
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdealQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCokernelsOnSite
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage
public import StacksFrontier.AlgebraicGeometry.Spaces.SupportedSectionsSubsheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.ZeroScheme

/-!
# Strict transforms of modules and of spaces over an algebraic space

Let `S` be a scheme, let `A` be an algebraic space over `S`, let `b : A' ⟶ A` be a morphism of
algebraic spaces over `S` and let `E ⊆ A'` be a subspace of its source.  For an algebraic space
`f : X ⟶ A` over `A` one forms the cartesian square

```
X ×_A A' --pr_{A'}--> A'
   |                   |
 pr_X                  b
   |                   |
   v                   v
   X -------f--------> A
```

and the set of points `|pr_{A'}^{-1}E|` of `X ×_A A'`.  The *strict transform* of an
`𝒪_X`-module `F` is the quotient of `pr_X^*F` by the submodule of those of its sections that are
supported on `|pr_{A'}^{-1}E|`, and the *strict transform of `X`* is the closed subspace of
`X ×_A A'` cut out by the ideal of those sections of `𝒪_{X ×_A A'}` that are supported on
`|pr_{A'}^{-1}E|`.

Stacks 0862 states both for `b` the blowup of `A` in a closed subspace `Z ⊆ A` and `E = b^{-1}Z`
the exceptional divisor of that blowup.  Neither construction uses anything of the pair `(b, E)`
beyond a morphism and a subspace of its source, so both are carried out here for an arbitrary
such pair; they specialize to the strict transform with respect to the blowup of `A` in `Z` on
taking `b` that blowup and `E` its exceptional divisor.  It is the *pair*, and not the morphism
alone, that is the correct datum: the strict transform depends on the closed subspace `Z` and not
only on the morphism `A' ⟶ A`, as the remark following Stacks 0862 records.

The base algebraic space of the chapter is written `A` here, and the blowup `B'` of the chapter
is written `A'`, the name `B` being taken by the ambient big fppf site.

## Main definitions

* `AlgebraicGeometry.Space.strictTransformPullback` is `X ×_A A'`, with projections
  `AlgebraicGeometry.Space.strictTransformPullbackToSource` and
  `AlgebraicGeometry.Space.strictTransformPullbackToBlowUp`.
* `AlgebraicGeometry.Space.exceptionalPreimage` is the subspace `pr_{A'}^{-1}E` of `X ×_A A'`,
  and `AlgebraicGeometry.Space.exceptionalPreimageSet` the set of points `|pr_{A'}^{-1}E|`.
* `AlgebraicGeometry.Space.strictTransformSheaf` is the strict transform of an `𝒪_X`-module.
* `AlgebraicGeometry.Space.strictTransformIdealSubmodule` is the ideal of sections of
  `𝒪_{X ×_A A'}` supported on `|pr_{A'}^{-1}E|`.
* `AlgebraicGeometry.Space.strictTransformSubfunctor` is the subfunctor underlying the strict
  transform of `X`, and `AlgebraicGeometry.Space.strictTransform` bundles it with its closedness.

## Main results

* `AlgebraicGeometry.Space.range_pointsMap_preimage_ι`: the points of a preimage subfunctor are
  the preimage of the points of the subfunctor, with no hypothesis.  Its instance
  `AlgebraicGeometry.Space.exceptionalPreimageSet_eq_preimage` identifies `|pr_{A'}^{-1}E|` with
  `|pr_{A'}|^{-1}|E|`, so the tag's own spelling of the supported set and the naive preimage
  spelling agree.
* `AlgebraicGeometry.Space.exceptionalPreimage_isClosedSubspace`: the preimage of a closed
  subspace `E` is a closed subspace, by Stacks 083Q.
* `AlgebraicGeometry.Space.strictTransformSubfunctor_isClosedSubspace`: the subfunctor of part
  (2) is a closed subspace.
* `AlgebraicGeometry.Space.strictTransformSubfunctor_eq_of_definingIdealSheaf_eq`: whenever some
  closed subspace has `AlgebraicGeometry.Space.strictTransformIdealSubmodule` as its defining
  ideal sheaf, the strict transform of `X` is that closed subspace.
* `AlgebraicGeometry.Space.strictTransform_exists_of_cartesian`: such a closed subspace exists as
  soon as the ideal of supported sections is cartesian on the affine étale charts.

## Implementation notes

The module universe is forced to be the universe `u` of the structure rings, as it is for the
inverse image `AlgebraicGeometry.Space.modulePullback` of Stacks 03LU, whose implementation notes
record the reason: the direct image of sheaves on the small étale sites is assembled from the
comparison equivalence of Stacks 03G1, which is available only at `Type u`, so its left adjoint
exists at no other module universe.  Cokernels of `𝒪_F`-modules are likewise available at that
universe, `AlgebraicGeometry.Space.hasCokernel_modules`, and the quotient of part (1) is
expressed as the cokernel of the inclusion
`SheafOfModules.Submodule.ι` of the supported-sections submodule of Stacks 0859.

The morphism `b` and the subspace `E` are hypotheses here rather than constructions, which keeps
this file independent of how the blowup is built.  The blowup of an algebraic space in a closed
subspace, Stacks 085Q, is now available and unconditional —
`AlgebraicGeometry.Space.blowUpAlong'` and `AlgebraicGeometry.Space.blowUpAlongHom'` in
`StacksFrontier.AlgebraicGeometry.Spaces.BlowupEquivalenceRelationClosed`, with
`AlgebraicGeometry.Space.exceptionalDivisor'` for `b⁻¹(Z)` — so the specialization described
above can be carried out by instantiating `b` and `E` at those.

Part (2) is the infimum, in the complete lattice of subfunctors of `X ×_A A'`, of those closed
subspaces whose defining ideal of Stacks 03MB is dominated at every affine étale chart by the
ideal of supported sections.  That is the construction Stacks 0845 is given by in
`StacksFrontier.AlgebraicGeometry.Spaces.ZeroScheme`, and for the same reason: the library has no
passage from a prescribed ideal to a closed subspace that is unconditional in the ideal.  The
infimum is a closed subspace by `AlgebraicGeometry.Space.isClosedSubspace_sInf` whatever the
ideal is, and it is the *right* closed subspace whenever the subspace cut out by the ideal exists
at all — that is
`AlgebraicGeometry.Space.strictTransformSubfunctor_eq_of_definingIdealSheaf_eq`, whose two halves
are `sInf_le` and the injectivity half of Stacks 03MB,
`AlgebraicGeometry.Space.le_of_forall_definingIdealAt_le`.  Existence is supplied by
`AlgebraicGeometry.Space.exists_definingIdealSheaf_eq_of_isCartesianOnAffineCharts` from
cartesianity of the ideal on the affine charts, and
`AlgebraicGeometry.Space.isCartesianOnAffineCharts_submodule_unit_of_surjective` reduces that
cartesianity to surjectivity of the base change comparison, injectivity being automatic for a
sheaf of ideals.  Affineness of a chart is spelled as in
`AlgebraicGeometry.Space.le_of_forall_definingIdealAt_le`, through
`AlgebraicGeometry.BigFppfOver.toScheme`, so that that lemma applies to the defining condition
without an intervening comparison.

## What is not proved

Quasi-coherence of the strict transform of a module, and quasi-coherence of the ideal of
part (2), are *not* established.  Over the blowup they rest on the preamble of the section
containing Stacks 0862: that the exceptional divisor `E` is an effective Cartier divisor, that
its preimage `pr_{A'}^{-1}E` is therefore locally principal, and that the inclusion of the
complement of a locally principal closed subspace is affine, hence that the complement is
retrocompact and Stacks 07ZP applies to the supported-sections ideal.  Two of the three are
available: effective Cartier divisors on an algebraic space are
`AlgebraicGeometry.Space.IsEffectiveCartierDivisor` in
`StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierDivisor`, and the blowup of Stacks 085Q is
`AlgebraicGeometry.Space.blowUpAlong'`.  What is still missing for algebraic spaces is the third,
affineness of the inclusion of the complement of a locally principal closed subspace — the
affineness half of Stacks 07ZU, proved for schemes as
`Stacks.Divisors.isAffineHom_compl_of_isEffectiveCartierDivisor`.  For part (1) quasi-coherence of
a cokernel of quasi-coherent modules on the small étale site would be needed on top of that, and
`StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCokernelsOnSite` supplies cokernels but not
their quasi-coherence.  Accordingly no quasi-coherence hypothesis is carried on the input module
either: the tag states part (1) for a quasi-coherent `F`, and the construction uses nothing of
`F`.

## References

* [Stacks Project, Tag 0862](https://stacks.math.columbia.edu/tag/0862)
* [Stacks Project, Tag 0859](https://stacks.math.columbia.edu/tag/0859)
* [Stacks Project, Tag 0845](https://stacks.math.columbia.edu/tag/0845)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 083Q](https://stacks.math.columbia.edu/tag/083Q)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The points of a preimage subfunctor -/

section Points

variable {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **The points of `f^{-1}Z` are the preimage of the points of `Z`**, for an arbitrary
morphism `f` and an arbitrary subfunctor `Z` of its target.

The square defining `CategoryTheory.Subfunctor.preimage` is cartesian, so Stacks 03H4 in the
form `AlgebraicGeometry.Space.preimage_image_pointsMap_of_isPullback` computes the image of the
points of `f^{-1}Z` under `|f|` as the preimage of the points of `Z` intersected with the whole
space, which is the assertion. -/
theorem range_pointsMap_preimage_ι (f : G ⟶ F) (Z : Subfunctor F) :
    Set.range (pointsMap B S hS (Z.preimage f).toFunctor (Z.preimage f).ι) =
      pointsMap B S hS G f ⁻¹' Set.range (pointsMap B S hS Z.toFunctor Z.ι) := by
  have h := preimage_image_pointsMap_of_isPullback B S hS
    (Subfunctor.isPullback_preimage f Z) Set.univ
  simpa [Set.image_univ] using h.symm

end Points

/-! ### The ambient base change and the preimage of the exceptional divisor -/

section Ambient

variable {A X A' : AlgebraicSpaces B S hS} (f : X ⟶ A) (b : A' ⟶ A)

/-- The fibre product `X ×_A A'` of an algebraic space `f : X ⟶ A` over `A` with a morphism
`b : A' ⟶ A`, in which both strict transforms live. -/
noncomputable abbrev strictTransformPullback : AlgebraicSpaces B S hS :=
  AlgebraicSpaces.fiberProduct B S hS f b

/-- The projection `pr_X : X ×_A A' ⟶ X`. -/
noncomputable abbrev strictTransformPullbackToSource :
    strictTransformPullback B S hS f b ⟶ X :=
  ObjectProperty.homMk (pullback.fst f.hom b.hom)

/-- The projection `pr_{A'} : X ×_A A' ⟶ A'`.  For `b` the blowup of `A` in a closed subspace
this is the projection to the blowup. -/
noncomputable abbrev strictTransformPullbackToBlowUp :
    strictTransformPullback B S hS f b ⟶ A' :=
  ObjectProperty.homMk (pullback.snd f.hom b.hom)

/-- The subspace `pr_{A'}^{-1}E` of `X ×_A A'`, the preimage of a subspace `E` of `A'` along the
projection `pr_{A'}`. -/
noncomputable abbrev exceptionalPreimage (E : Subfunctor A'.1) :
    Subfunctor (strictTransformPullback B S hS f b).1 :=
  E.preimage (strictTransformPullbackToBlowUp B S hS f b).hom

/-- The set of points `|pr_{A'}^{-1}E|` of `X ×_A A'` on which the sections cut out by the strict
transform are supported. -/
noncomputable abbrev exceptionalPreimageSet (E : Subfunctor A'.1) :
    Set (points B S hS (strictTransformPullback B S hS f b).1) :=
  Set.range (pointsMap B S hS (exceptionalPreimage B S hS f b E).toFunctor
    (exceptionalPreimage B S hS f b E).ι)

/-- The set of points `|pr_{A'}^{-1}E|` is the preimage of `|E|` under `|pr_{A'}|`, so the
spelling of the supported set used in Stacks 0862 and the naive preimage spelling agree. -/
theorem exceptionalPreimageSet_eq_preimage (E : Subfunctor A'.1) :
    exceptionalPreimageSet B S hS f b E =
      pointsMap B S hS (strictTransformPullback B S hS f b).1
          (strictTransformPullbackToBlowUp B S hS f b).hom ⁻¹'
        Set.range (pointsMap B S hS E.toFunctor E.ι) :=
  range_pointsMap_preimage_ι B S hS _ E

/-- **Stacks 083Q.** The preimage `pr_{A'}^{-1}E` of a closed subspace `E ⊆ A'` is a closed
subspace of `X ×_A A'`. -/
theorem exceptionalPreimage_isClosedSubspace (E : Subfunctor A'.1)
    (hE : IsClosedSubspace B S hS E) :
    IsClosedSubspace B S hS (exceptionalPreimage B S hS f b E) :=
  isClosedSubspace_preimage B S hS _ E A'.2 (strictTransformPullback B S hS f b).2 hE

end Ambient

/-! ### The strict transform of a module -/

section ModuleTransform

variable {A X A' : AlgebraicSpaces B S hS} (f : X ⟶ A) (b : A' ⟶ A)

/-- **Stacks 0862, part (1).** The strict transform of an `𝒪_X`-module `F` along a morphism
`b : A' ⟶ A` relative to a subspace `E ⊆ A'`: pull `F` back to `X ×_A A'` along `pr_X` and divide
out the submodule of those sections that are supported on `|pr_{A'}^{-1}E|`.

Stated for an arbitrary morphism `b` together with an arbitrary subspace `E` of its source, this
specializes to the strict transform with respect to the blowup of `A` in a closed subspace
`Z ⊆ A` on taking `b` that blowup and `E = b^{-1}Z` its exceptional divisor.  Stacks 0862 states
the construction for a quasi-coherent `F`, which is the case it is applied in; the construction
itself uses nothing of `F`, so no quasi-coherence hypothesis is carried here.

Quasi-coherence of the strict transform is *not* asserted: it would need the preamble of the
section containing Stacks 0862 — that `E` is an effective Cartier divisor, that its preimage is
locally principal, and that the complement of the latter has an affine inclusion — none of which
is available for algebraic spaces, together with quasi-coherence of a cokernel on the small étale
site.  See the module documentation. -/
@[stacks 0862 "strict transform of a module"]
noncomputable def strictTransformSheaf (E : Subfunctor A'.1)
    (F : Modules.{u, u} B S hS X.1 X.2) :
    Modules.{u, u} B S hS (strictTransformPullback B S hS f b).1
      (strictTransformPullback B S hS f b).2 :=
  cokernel (supportedSectionsSubmodule B S hS (strictTransformPullback B S hS f b).1
    (strictTransformPullback B S hS f b).2 (exceptionalPreimageSet B S hS f b E)
    ((modulePullback B S hS (strictTransformPullbackToSource B S hS f b)).obj F)).ι

end ModuleTransform

/-! ### The strict transform of an algebraic space -/

section SpaceTransform

variable {A X A' : AlgebraicSpaces B S hS} (f : X ⟶ A) (b : A' ⟶ A)

/-- The ideal of those sections of `𝒪_{X ×_A A'}` that are supported on `|pr_{A'}^{-1}E|`, as a
sheaf submodule of the structure sheaf on the small étale site of `X ×_A A'`.

Quasi-coherence of this ideal is *not* asserted; see the module documentation. -/
noncomputable abbrev strictTransformIdealSubmodule (E : Subfunctor A'.1) :
    (SheafOfModules.unit
      (structureRingSheaf B S hS (strictTransformPullback B S hS f b))).Submodule :=
  supportedSectionsSubmodule B S hS (strictTransformPullback B S hS f b).1
    (strictTransformPullback B S hS f b).2 (exceptionalPreimageSet B S hS f b E)
    (SheafOfModules.unit (structureRingSheaf B S hS (strictTransformPullback B S hS f b)))

/-- The subfunctor of `X ×_A A'` underlying the strict transform of `X`: the intersection of
those closed subspaces whose defining ideal is dominated, at every affine étale chart, by the
ideal of sections supported on `|pr_{A'}^{-1}E|`. -/
noncomputable def strictTransformSubfunctor (E : Subfunctor A'.1) :
    Subfunctor (strictTransformPullback B S hS f b).1 :=
  sInf {Z | ∃ hZ : IsClosedSubspace B S hS Z,
    ∀ U : SmallEtale B S hS (strictTransformPullback B S hS f b).1,
      IsAffine ((BigFppfOver.toScheme B S hS).obj U.1.left) →
      definingIdealAt B S hS (strictTransformPullback B S hS f b) ⟨Z, hZ⟩ (op U) ≤
        (strictTransformIdealSubmodule B S hS f b E).toSubmodule.obj (op U)}

/-- The subfunctor underlying the strict transform of `X` is a closed subspace of `X ×_A A'`,
by Stacks 0845 in the form `AlgebraicGeometry.Space.isClosedSubspace_sInf`. -/
theorem strictTransformSubfunctor_isClosedSubspace (E : Subfunctor A'.1) :
    IsClosedSubspace B S hS (strictTransformSubfunctor B S hS f b E) :=
  isClosedSubspace_sInf B S hS (strictTransformPullback B S hS f b).2 _
    fun _ hZ => hZ.elim fun h _ => h

/-- **Stacks 0862, part (2).** The strict transform of an algebraic space `f : X ⟶ A` over `A`
along a morphism `b : A' ⟶ A` relative to a subspace `E ⊆ A'`: the closed subspace of `X ×_A A'`
determined by the ideal of those sections of `𝒪_{X ×_A A'}` that are supported on
`|pr_{A'}^{-1}E|`.

Stated for an arbitrary morphism `b` together with an arbitrary subspace `E` of its source, this
specializes to the strict transform with respect to the blowup of `A` in a closed subspace
`Z ⊆ A` on taking `b` that blowup and `E = b^{-1}Z` its exceptional divisor.

The closed subspace is realized as the infimum of those closed subspaces whose defining ideal is
dominated by that ideal of supported sections, which is a closed subspace unconditionally, and
which coincides with the closed subspace cut out by the ideal whenever the latter exists, by
`AlgebraicGeometry.Space.strictTransformSubfunctor_eq_of_definingIdealSheaf_eq`.

Quasi-coherence of the defining ideal is *not* asserted: it would need the preamble of the
section containing Stacks 0862 — that `E` is an effective Cartier divisor, that its preimage is
locally principal, and that the complement of the latter has an affine inclusion — none of which
is available for algebraic spaces.  See the module documentation. -/
@[stacks 0862 "strict transform of a space"]
noncomputable def strictTransform (E : Subfunctor A'.1) :
    ClosedSubspaces B S hS (strictTransformPullback B S hS f b).1 :=
  ⟨strictTransformSubfunctor B S hS f b E,
    strictTransformSubfunctor_isClosedSubspace B S hS f b E⟩

/-- **The strict transform is the closed subspace cut out by the ideal of supported sections,
whenever there is one.**  If a closed subspace `Z₀ ⊆ X ×_A A'` has the ideal of sections
supported on `|pr_{A'}^{-1}E|` as its defining ideal sheaf, then the strict transform of `X` is
`Z₀`.

One inclusion is that `Z₀` is a member of the intersected family.  The other is the injectivity
half of Stacks 03MB, `AlgebraicGeometry.Space.le_of_forall_definingIdealAt_le`: a member of the
family has, at every affine étale chart, defining ideal inside that of `Z₀`, hence contains
`Z₀`. -/
theorem strictTransformSubfunctor_eq_of_definingIdealSheaf_eq (E : Subfunctor A'.1)
    (Z₀ : ClosedSubspaces B S hS (strictTransformPullback B S hS f b).1)
    (hZ₀ : definingIdealSheaf B S hS (strictTransformPullback B S hS f b) Z₀ =
      strictTransformIdealSubmodule B S hS f b E) :
    strictTransformSubfunctor B S hS f b E = Z₀.1 := by
  refine le_antisymm (sInf_le ⟨Z₀.2, fun U _ => ?_⟩) (le_sInf ?_)
  · rw [← hZ₀]
    exact le_rfl
  · rintro Z ⟨hZ, hZle⟩
    refine le_of_forall_definingIdealAt_le B S hS _ Z₀ ⟨Z, hZ⟩ fun U hU => ?_
    rw [← hZ₀] at hZle
    exact hZle U hU

/-- **The strict transform of `X` is cut out by an ideal as soon as that ideal is cartesian on
the affine étale charts.**  The ideal of sections supported on `|pr_{A'}^{-1}E|` is then the
defining ideal sheaf of a closed subspace of `X ×_A A'`, which by
`AlgebraicGeometry.Space.strictTransformSubfunctor_eq_of_definingIdealSheaf_eq` is the strict
transform.

The hypothesis is the only one left: the passage from a sheaf of ideals to a closed subspace,
`AlgebraicGeometry.Space.exists_definingIdealSheaf_eq_of_isCartesianOnAffineCharts`, is
unconditional in everything else, and for a sheaf of ideals cartesianity on affine charts is
surjectivity of the base change comparison there, by
`AlgebraicGeometry.Space.isCartesianOnAffineCharts_submodule_unit_of_surjective`. -/
theorem strictTransform_exists_of_cartesian (E : Subfunctor A'.1)
    (h : IsCartesianOnAffineCharts
      (strictTransformIdealSubmodule B S hS f b E).toSheafOfModules) :
    ∃ Z : ClosedSubspaces B S hS (strictTransformPullback B S hS f b).1,
      definingIdealSheaf B S hS (strictTransformPullback B S hS f b) Z =
        strictTransformIdealSubmodule B S hS f b E :=
  exists_definingIdealSheaf_eq_of_isCartesianOnAffineCharts B S hS
    (strictTransformPullback B S hS f b) _ h

end SpaceTransform

end AlgebraicGeometry.Space

end
