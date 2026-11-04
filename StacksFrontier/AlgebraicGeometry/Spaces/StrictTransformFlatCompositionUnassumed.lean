module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffinePushforwardQuasicoherentExact
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupIsomorphismOffCentre
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatAtPointBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleSupportedSections
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformEtaleRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformExceptionalPreimage
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformSheafBlowupComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformSpaceComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformSpaceEtaleRestriction

/-!
# Stacks 0865 and 0868 on the source's own hypotheses

`StacksFrontier/AlgebraicGeometry/Spaces/StrictTransformProperties.lean` states the two parts of
Stacks 0865 and the two parts of Stacks 0868 with one assumed input each, named `hloc` there.
Every one of those inputs is now a theorem, so this file restates the four conclusions with
nothing assumed beyond what the source assumes, and carries the two tags.

The four statements keep the names of their conditional forms with the suffix `_unconditional`
appended; nothing about the conclusions differs.

## Main results

* `AlgebraicGeometry.Space.strictTransformSubfunctor_eq_top_of_isFlatAt_unconditional`
  is **Stacks 0865, part (1)**.
* `Space.isIso_strictTransformSheafQuotient_of_isFlatOverAtGeometricPoint_unconditional`
  is **Stacks 0865, part (2)**.
* `AlgebraicGeometry.Space.exists_strictTransformSheaf_comp_iso_unconditional`
  is **Stacks 0868, part (1)**.
* `AlgebraicGeometry.Space.exists_strictTransformSpace_comp_iso_unconditional`
  is **Stacks 0868, part (2)**.

## Implementation notes

The inputs discharged are, in order: that the ideal of sections of `𝒪_{X ×_A A'}` supported on
the exceptional preimage vanishes on every affine étale chart
(`AlgebraicGeometry.Space.strictTransformIdealSubmodule_eq_bot_of_isFlatAt`); that the inclusion
of the submodule of sections of `pr_X^*F` supported there is zero for a quasi-coherent `F`
(`Space.supportedSections_exceptionalPreimage_ι_eq_zero_of_isFlatOverAtGeometricPoint`);
and, for the two parts of Stacks 0868, the comparison of the iterated strict transform with the
strict transform along the composite, on modules
(`AlgebraicGeometry.Space.exists_iteratedStrictTransformSheaf_iso`) and on spaces
(`AlgebraicGeometry.Space.exists_iteratedStrictTransformSpace_iso`).

## References

* [Stacks Project, Tag 0862](https://stacks.math.columbia.edu/tag/0862)
* [Stacks Project, Tag 0863](https://stacks.math.columbia.edu/tag/0863)
* [Stacks Project, Tag 0865](https://stacks.math.columbia.edu/tag/0865)
* [Stacks Project, Tag 0868](https://stacks.math.columbia.edu/tag/0868)
* [Stacks Project, Tag 085U](https://stacks.math.columbia.edu/tag/085U)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 05VU](https://stacks.math.columbia.edu/tag/05VU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

/- The global instances `Abelian (SheafOfModules.{max u v r w} O)` and its Grothendieck
counterpart leave a stuck universe constraint against modules in the pinned universe `u + 1`. -/
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Flat

variable {A X A' : AlgebraicSpaces B S hS} (f : X ⟶ A) (b : A' ⟶ A)

/-- **Stacks 0865, part (1).** Let `Z ⊆ A` be a closed subspace of an algebraic space over `S`,
let `b : A' ⟶ A` be the blowup of `A` in `Z` and let `f : X ⟶ A` be an algebraic space over
`A`.  If `X` is flat over `A` at every point lying over `Z`, then the strict transform of `X`
with respect to `b` is the whole base change `X ×_A A'`.

The hypotheses are the source's and nothing else.  The ideal of sections of `𝒪_{X ×_A A'}`
supported on the exceptional preimage vanishes on every étale chart,
`AlgebraicGeometry.Space.strictTransformIdealSubmodule_eq_bot_of_isFlatAt`; the strict
transform is then the whole base change by Stacks 03MB, in the form
`AlgebraicGeometry.Space.strictTransformSubfunctor_eq_top_of_forall_definingIdealAt_eq_bot`.

The source reduces part (1) to the case of schemes by étale localization, Stacks 0863 parts (2)
and (3), which this library does not have; the route taken instead is native to algebraic
spaces and runs through the étale charts of the fibre product.  See the module documentation of
`StacksFrontier/AlgebraicGeometry/Spaces/FlatAtPointBaseChange.lean`.

The conditional form of this statement in
`StacksFrontier/AlgebraicGeometry/Spaces/StrictTransformProperties.lean` keeps the name
without the suffix `_unconditional`; the suffix marks the same conclusion with that form's
assumed input discharged, and the tag is registered here. -/
@[stacks 0865 "part (1), with no assumed inputs"]
theorem strictTransformSubfunctor_eq_top_of_isFlatAt_unconditional (Z : ClosedSubspaces B S hS A.1)
    (hb : IsBlowupAlong B S hS Z b)
    (hflat : ∀ x : points B S hS X.1,
      pointsMap B S hS X.1 f.hom x ∈ Set.range (pointsMap B S hS Z.1.toFunctor Z.1.ι) →
        IsFlatAt B S hS f.hom x) :
    strictTransformSubfunctor B S hS f b (Z.1.preimage b.hom) = ⊤ :=
  strictTransformSubfunctor_eq_top_of_forall_definingIdealAt_eq_bot B S hS f b _
    fun U _ => strictTransformIdealSubmodule_eq_bot_of_isFlatAt B S hS f b Z hb hflat U

/-- **Stacks 0865, part (2).** In the situation of part (1), let `F` be a quasi-coherent
`𝒪_X`-module which is flat over `A` at every point lying over `Z`.  Then the canonical quotient
map `pr_X^*F ⟶ F'` onto the strict transform of `F` is an isomorphism, so the strict transform
of `F` is `pr_X^*F`.

The hypotheses are the source's and nothing else: `b` is the blowup of `A` in `Z` in the sense
of the universal property of Stacks 085U, `F` is quasi-coherent, and `F` is flat over `A` at the
points above `Z` — read at geometric points, condition (2) of Stacks 05VU,
`AlgebraicGeometry.Space.IsFlatOverAtGeometricPoint`, a geometric point lying over `Z` when its
underlying point of `|X|` does.

The submodule of sections of `pr_X^*F` supported on the exceptional preimage vanishes,
`Space.supportedSections_exceptionalPreimage_ι_eq_zero_of_isFlatOverAtGeometricPoint`;
the strict transform is the cokernel of its inclusion, so the quotient map is the cokernel
projection of a zero morphism and hence invertible.

The source reduces part (2) to the case of schemes by étale localization, Stacks 0863 parts (2)
and (3); the route taken instead is native to algebraic spaces and runs through the étale charts
of the fibre product, exactly as for part (1).  See the module documentation of
`StacksFrontier/AlgebraicGeometry/Spaces/FlatModuleSupportedSections.lean`.

The conditional form of this statement in
`StacksFrontier/AlgebraicGeometry/Spaces/StrictTransformProperties.lean` keeps the name
without the suffix `_unconditional`; the suffix marks the same conclusion with that form's
assumed input discharged, and the tag is registered here. -/
@[stacks 0865 "part (2), with no assumed inputs"]
theorem isIso_strictTransformSheafQuotient_of_isFlatOverAtGeometricPoint_unconditional
    (Z : ClosedSubspaces B S hS A.1) (F : Modules.{u, u} B S hS X.1 X.2)
    (hF : F.IsQuasicoherentOnSite) (hb : IsBlowupAlong B S hS Z b)
    (hflat : ∀ xbar : GeometricPoint B S hS X.1,
      pointsMap B S hS X.1 f.hom xbar.image ∈
          Set.range (pointsMap B S hS Z.1.toFunctor Z.1.ι) →
        IsFlatOverAtGeometricPoint B S hS f F xbar) :
    IsIso (strictTransformSheafQuotient B S hS f b (Z.1.preimage b.hom) F) :=
  cokernel.π_of_zero
    (supportedSections_exceptionalPreimage_ι_eq_zero_of_isFlatOverAtGeometricPoint B S hS f b Z
      hb F hF hflat)

end Flat

section Composition

variable {A X A' A'' : AlgebraicSpaces B S hS} (f : X ⟶ A) (b : A' ⟶ A) (c : A'' ⟶ A')

/-- **Stacks 0868, part (1).** Let `Z ⊆ A` be a closed subspace of an algebraic space over `S`,
let `b : A' ⟶ A` be the blowup of `A` in `Z`, let `Z' ⊆ A'` be a closed subspace and let
`c : A'' ⟶ A'` be the blowup of `A'` in `Z'`.  Let `Y ⊆ A` be a closed subspace with
`|Y| = |Z| ∪ |b|(|Z'|)` and such that the composition `A'' ⟶ A` is the blowup of `A` in `Y`.
Then for any algebraic space `f : X ⟶ A` over `A` and any `𝒪_X`-module `F`, the strict
transform of `F` with respect to `c` of the strict transform of `F` with respect to `b` is the
strict transform of `F` with respect to `A'' ⟶ A`, compatibly with the identification of the
two ambient base changes and with the quotient maps onto the two strict transforms.

The identification of the ambient base changes `(X ×_A A') ×_{A'} A'' ≅ X ×_A A''`, together
with its compatibility with the projections to `X` and to `A''` — the two equations of the
conclusion, the first of which the comparison of the modules is stated relative to — is
`AlgebraicGeometry.Space.iteratedStrictTransformPullbackIso`, and is proved here
unconditionally.

The comparison of the modules themselves, the last conjunct, is produced with its compatibility
with the two quotient maps onto the strict transforms: pulled back along the identification of
the ambient base changes, the quotient map `pr_X^*F ⟶ F'` for the composite blowup becomes, over
the induced identification of the two pullbacks of `F`
(`AlgebraicGeometry.Space.strictTransformInnerModulePullbackIso`), the composite of the pullback
of the first quotient map with the second.  Since the first of those is an epimorphism, there is
exactly one isomorphism which does that; that is the sense in which the comparison is canonical.

Its two halves are `AlgebraicGeometry.Space.exists_iteratedStrictTransformSheaf_iso` of
`StacksFrontier/AlgebraicGeometry/Spaces/StrictTransformComposition.lean` — which carries the
compatibility of the iterated quotient with the two projections — and the universal property of
the quotient by the supported sections,
`AlgebraicGeometry.Space.exists_strictTransformSheafIso`, applied to the pullback of the
quotient map for the composite blowup along the ambient identification.  That pullback is an
epimorphism because the pullback of modules is a left adjoint; it kills only the sections
supported on the exceptional preimage of `(c ≫ b)⁻¹Y` because over the part of
`(X ×_A A') ×_{A'} A''` lying off that set it is invertible
(`AlgebraicGeometry.Space.isIso_modulePullback_map_cokernelπ_supportedSectionsSubmodule`, the
points there missing the exceptional preimage downstairs), which is
`AlgebraicGeometry.Space.kernelSectionsSupportedIn_of_mono_modulePullback_map`; and its target
has no nonzero local section supported there because the restriction of the strict transform
along that identification is the strict transform of the restriction, Stacks 0863 part (3) in
its geometry-free form
`AlgebraicGeometry.Space.strictTransformSheafEtaleRestrictionIso` — applicable because the
identification is an isomorphism, hence étale.

The hypothesis of the iterated comparison on the supported sets is
`AlgebraicGeometry.Space.exceptionalPreimageSet_compositeCentre`, which is where `hY` and the
blowup `b` are used: a blowup is injective on the points off its centre, so the exceptional
preimage of `(c ≫ b)⁻¹Y` splits as the inverse image of the first exceptional preimage together
with the exceptional preimage of `c⁻¹Z'`.

The conditional form of this statement in
`StacksFrontier/AlgebraicGeometry/Spaces/StrictTransformProperties.lean` keeps the name
without the suffix `_unconditional`; the suffix marks the same conclusion with that form's
assumed input discharged, and the tag is registered here. -/
@[stacks 0868 "part (1): the strict transform of a module for the blowup of the base in the \
composite centre is the strict transform along the second blowup of the strict transform along \
the first, by the isomorphism carrying the pullback of the quotient map onto the former to the \
composite of the two quotient maps onto the latter, over the identification of the two ambient \
base changes and the identification of the two pullbacks of the module it induces; for an \
arbitrary module and with no assumed inputs"]
theorem exists_strictTransformSheaf_comp_iso_unconditional (Z : ClosedSubspaces B S hS A.1)
    (Z' : ClosedSubspaces B S hS A'.1) (Y : ClosedSubspaces B S hS A.1)
    (F : Modules.{u, u} B S hS X.1 X.2)
    (hb : IsBlowupAlong B S hS Z b) (hc : IsBlowupAlong B S hS Z' c)
    (hY : IsCompositeCentre B S hS b Z Z' Y) (_hd : IsBlowupAlong B S hS Y (c ≫ b)) :
    ∃ e : strictTransformPullback B S hS (strictTransformPullbackToBlowUp B S hS f b) c ≅
        strictTransformPullback B S hS f (c ≫ b),
      ∃ hsrc : e.hom ≫ strictTransformPullbackToSource B S hS f (c ≫ b) =
          strictTransformPullbackToSource B S hS
              (strictTransformPullbackToBlowUp B S hS f b) c ≫
            strictTransformPullbackToSource B S hS f b,
      (e.hom ≫ strictTransformPullbackToBlowUp B S hS f (c ≫ b) =
        strictTransformPullbackToBlowUp B S hS
          (strictTransformPullbackToBlowUp B S hS f b) c) ∧
      ∃ cmp : (modulePullback B S hS e.hom).obj
            (strictTransformSheaf B S hS f (c ≫ b) (Y.1.preimage (c ≫ b).hom) F) ≅
          strictTransformSheaf B S hS (strictTransformPullbackToBlowUp B S hS f b) c
            (Z'.1.preimage c.hom) (strictTransformSheaf B S hS f b (Z.1.preimage b.hom) F),
        (modulePullback B S hS e.hom).map
              (strictTransformSheafQuotient B S hS f (c ≫ b)
                (Y.1.preimage (c ≫ b).hom) F) ≫ cmp.hom =
          (strictTransformInnerModulePullbackIso B S hS f (c ≫ b)
              (strictTransformPullbackToSource B S hS f b)
              (strictTransformPullbackToBlowUp B S hS f b) c e.hom hsrc F).hom ≫
            (modulePullback B S hS (strictTransformPullbackToSource B S hS
                  (strictTransformPullbackToBlowUp B S hS f b) c)).map
                (strictTransformSheafQuotient B S hS f b (Z.1.preimage b.hom) F) ≫
              strictTransformSheafQuotient B S hS
                (strictTransformPullbackToBlowUp B S hS f b) c (Z'.1.preimage c.hom)
                (strictTransformSheaf B S hS f b (Z.1.preimage b.hom) F) := by
  refine ⟨iteratedStrictTransformPullbackIso B S hS f b c,
    iteratedStrictTransformPullbackIso_hom_toSource B S hS f b c,
    iteratedStrictTransformPullbackIso_hom_toBlowUp B S hS f b c, ?_⟩
  set inner := strictTransformInnerModulePullbackIso B S hS f (c ≫ b)
    (strictTransformPullbackToSource B S hS f b)
    (strictTransformPullbackToBlowUp B S hS f b) c
    (iteratedStrictTransformPullbackIso B S hS f b c).hom
    (iteratedStrictTransformPullbackIso_hom_toSource B S hS f b c) F with hinner
  -- The exceptional preimage of `(c ≫ b)⁻¹Y` upstairs is a closed set of points, and it is the
  -- inverse image of the exceptional preimage on `X ×_A A''`.
  have hTcl : IsClosed (exceptionalPreimageSet B S hS
      (strictTransformPullbackToBlowUp B S hS f b) c (Y.1.preimage (c ≫ b).hom)) :=
    isClosed_exceptionalPreimageSet B S hS (strictTransformPullbackToBlowUp B S hS f b) c _
      (isClosedSubspace_preimage B S hS (c ≫ b).hom Y.1 A.2 A''.2 Y.2)
  have hpre : exceptionalPreimageSet B S hS
        (strictTransformPullbackToBlowUp B S hS f b) c (Y.1.preimage (c ≫ b).hom) =
      pointsMap B S hS (strictTransformPullback B S hS
            (strictTransformPullbackToBlowUp B S hS f b) c).1
          (iteratedStrictTransformPullbackIso B S hS f b c).hom.hom ⁻¹'
        exceptionalPreimageSet B S hS f (c ≫ b) (Y.1.preimage (c ≫ b).hom) :=
    exceptionalPreimageSet_eq_preimage_of_comp_eq B S hS f (c ≫ b)
      (Y.1.preimage (c ≫ b).hom) (strictTransformPullbackToBlowUp B S hS f b) c
      (Y.1.preimage (c ≫ b).hom) (𝟙 A'')
      (iteratedStrictTransformPullbackIso B S hS f b c).hom
      (by rw [iteratedStrictTransformPullbackIso_hom_toBlowUp, Category.comp_id])
      (by simp)
  -- The pullback of the quotient map along the ambient identification is an epimorphism, the
  -- pullback of modules being a left adjoint.
  have hepi : Epi ((modulePullback B S hS
      (iteratedStrictTransformPullbackIso B S hS f b c).hom).map
        (strictTransformSheafQuotient B S hS f (c ≫ b) (Y.1.preimage (c ≫ b).hom) F)) := by
    have := (modulePullbackAdjunction B S hS
      (iteratedStrictTransformPullbackIso B S hS f b c).hom).leftAdjoint_preservesColimits.{u, u}
    have : Epi (strictTransformSheafQuotient B S hS f (c ≫ b)
        (Y.1.preimage (c ≫ b).hom) F) :=
      inferInstanceAs (Epi (cokernel.π (strictTransformSupportedSections B S hS f (c ≫ b)
        (Y.1.preimage (c ≫ b).hom) F).ι))
    exact Functor.map_epi _ _
  have hqe : Epi (inner.inv ≫ (modulePullback B S hS
      (iteratedStrictTransformPullbackIso B S hS f b c).hom).map
        (strictTransformSheafQuotient B S hS f (c ≫ b) (Y.1.preimage (c ≫ b).hom) F)) := by
    have := hepi
    exact epi_comp _ _
  -- Its target has no nonzero local section supported on that set: along the ambient
  -- identification the strict transform restricts to the strict transform of the restriction,
  -- which is a quotient by exactly the sections supported there.
  have hnos : HasNoSectionsSupportedIn B S hS
      (strictTransformPullback B S hS (strictTransformPullbackToBlowUp B S hS f b) c)
      (exceptionalPreimageSet B S hS (strictTransformPullbackToBlowUp B S hS f b) c
        (Y.1.preimage (c ≫ b).hom))
      ((modulePullback B S hS (iteratedStrictTransformPullbackIso B S hS f b c).hom).obj
        (strictTransformSheaf B S hS f (c ≫ b) (Y.1.preimage (c ≫ b).hom) F)) :=
    hasNoSectionsSupportedIn_of_iso B S hS _
      (strictTransformSheafEtaleRestrictionIso B S hS f (c ≫ b)
        (Y.1.preimage (c ≫ b).hom) (strictTransformPullbackToSource B S hS f b)
        (strictTransformPullbackToBlowUp B S hS f b) c (Y.1.preimage (c ≫ b).hom) (𝟙 A'')
        (iteratedStrictTransformPullbackIso B S hS f b c).hom (isEtale_of_isIso B S hS _)
        (iteratedStrictTransformPullbackIso_hom_toSource B S hS f b c)
        (by rw [iteratedStrictTransformPullbackIso_hom_toBlowUp, Category.comp_id])
        (by simp) F)
      (hasNoSectionsSupportedIn_cokernel_supportedSectionsSubmodule B S hS
        (strictTransformPullback B S hS (strictTransformPullbackToBlowUp B S hS f b) c)
        (exceptionalPreimageSet B S hS (strictTransformPullbackToBlowUp B S hS f b) c
          (Y.1.preimage (c ≫ b).hom)) hTcl
        ((modulePullback B S hS (strictTransformPullbackToSource B S hS
            (strictTransformPullbackToBlowUp B S hS f b) c)).obj
          ((modulePullback B S hS (strictTransformPullbackToSource B S hS f b)).obj F)))
  -- It kills only the sections supported on that set: over the open part lying off it the
  -- quotient map pulls back to an isomorphism, no point there lying over the exceptional
  -- preimage downstairs.
  have hjE : IsEtale B S hS (openOffSubspaceι B S hS
      (strictTransformPullback B S hS (strictTransformPullbackToBlowUp B S hS f b) c)
      (exceptionalPreimageSet B S hS (strictTransformPullbackToBlowUp B S hS f b) c
        (Y.1.preimage (c ≫ b).hom)) hTcl).hom :=
    isEtale_openOffSubspaceι B S hS _ _ hTcl
  have hjcomp : IsEtale B S hS ((openOffSubspaceι B S hS
        (strictTransformPullback B S hS (strictTransformPullbackToBlowUp B S hS f b) c)
        (exceptionalPreimageSet B S hS (strictTransformPullbackToBlowUp B S hS f b) c
          (Y.1.preimage (c ≫ b).hom)) hTcl ≫
      (iteratedStrictTransformPullbackIso B S hS f b c).hom).hom) :=
    isEtale_comp B S hS hjE (isEtale_of_isIso B S hS _)
  have hmiss : ∀ v : points B S hS (openOffSubspace B S hS
        (strictTransformPullback B S hS (strictTransformPullbackToBlowUp B S hS f b) c)
        (exceptionalPreimageSet B S hS (strictTransformPullbackToBlowUp B S hS f b) c
          (Y.1.preimage (c ≫ b).hom)) hTcl).1,
      pointsMap B S hS _ (openOffSubspaceι B S hS
            (strictTransformPullback B S hS (strictTransformPullbackToBlowUp B S hS f b) c)
            (exceptionalPreimageSet B S hS (strictTransformPullbackToBlowUp B S hS f b) c
              (Y.1.preimage (c ≫ b).hom)) hTcl ≫
          (iteratedStrictTransformPullbackIso B S hS f b c).hom).hom v ∉
        exceptionalPreimageSet B S hS f (c ≫ b) (Y.1.preimage (c ≫ b).hom) := by
    intro v hv
    have h1 : pointsMap B S hS _ (openOffSubspaceι B S hS
        (strictTransformPullback B S hS (strictTransformPullbackToBlowUp B S hS f b) c)
        (exceptionalPreimageSet B S hS (strictTransformPullbackToBlowUp B S hS f b) c
          (Y.1.preimage (c ≫ b).hom)) hTcl).hom v ∈
        (exceptionalPreimageSet B S hS (strictTransformPullbackToBlowUp B S hS f b) c
          (Y.1.preimage (c ≫ b).hom))ᶜ := by
      rw [← range_pointsMap_openOffSubspaceι B S hS _ _ hTcl]
      exact Set.mem_range_self v
    have h2 : pointsMap B S hS _ (openOffSubspaceι B S hS
            (strictTransformPullback B S hS (strictTransformPullbackToBlowUp B S hS f b) c)
            (exceptionalPreimageSet B S hS (strictTransformPullbackToBlowUp B S hS f b) c
              (Y.1.preimage (c ≫ b).hom)) hTcl ≫
          (iteratedStrictTransformPullbackIso B S hS f b c).hom).hom v =
        pointsMap B S hS _ (iteratedStrictTransformPullbackIso B S hS f b c).hom.hom
          (pointsMap B S hS _ (openOffSubspaceι B S hS
            (strictTransformPullback B S hS (strictTransformPullbackToBlowUp B S hS f b) c)
            (exceptionalPreimageSet B S hS (strictTransformPullbackToBlowUp B S hS f b) c
              (Y.1.preimage (c ≫ b).hom)) hTcl).hom v) :=
      congrFun (pointsMap_comp B S hS _ (openOffSubspaceι B S hS
        (strictTransformPullback B S hS (strictTransformPullbackToBlowUp B S hS f b) c)
        (exceptionalPreimageSet B S hS (strictTransformPullbackToBlowUp B S hS f b) c
          (Y.1.preimage (c ≫ b).hom)) hTcl).hom
        (iteratedStrictTransformPullbackIso B S hS f b c).hom.hom) v
    rw [h2] at hv
    exact h1 ((Set.ext_iff.1 hpre _).2 hv)
  have hmono1 : Mono ((modulePullback B S hS (openOffSubspaceι B S hS
        (strictTransformPullback B S hS (strictTransformPullbackToBlowUp B S hS f b) c)
        (exceptionalPreimageSet B S hS (strictTransformPullbackToBlowUp B S hS f b) c
          (Y.1.preimage (c ≫ b).hom)) hTcl ≫
      (iteratedStrictTransformPullbackIso B S hS f b c).hom)).map
      (strictTransformSheafQuotient B S hS f (c ≫ b) (Y.1.preimage (c ≫ b).hom) F)) := by
    have hiso : IsIso ((modulePullback B S hS (openOffSubspaceι B S hS
          (strictTransformPullback B S hS (strictTransformPullbackToBlowUp B S hS f b) c)
          (exceptionalPreimageSet B S hS (strictTransformPullbackToBlowUp B S hS f b) c
            (Y.1.preimage (c ≫ b).hom)) hTcl ≫
        (iteratedStrictTransformPullbackIso B S hS f b c).hom)).map
        (strictTransformSheafQuotient B S hS f (c ≫ b) (Y.1.preimage (c ≫ b).hom) F)) :=
      isIso_modulePullback_map_cokernelπ_supportedSectionsSubmodule B S hS
        (openOffSubspaceι B S hS
          (strictTransformPullback B S hS (strictTransformPullbackToBlowUp B S hS f b) c)
          (exceptionalPreimageSet B S hS (strictTransformPullbackToBlowUp B S hS f b) c
            (Y.1.preimage (c ≫ b).hom)) hTcl ≫
          (iteratedStrictTransformPullbackIso B S hS f b c).hom) hjcomp
        (exceptionalPreimageSet B S hS f (c ≫ b) (Y.1.preimage (c ≫ b).hom)) hmiss
        ((modulePullback B S hS (strictTransformPullbackToSource B S hS f (c ≫ b))).obj F)
    have := hiso
    infer_instance
  have hmono2 : Mono ((modulePullback B S hS (openOffSubspaceι B S hS
        (strictTransformPullback B S hS (strictTransformPullbackToBlowUp B S hS f b) c)
        (exceptionalPreimageSet B S hS (strictTransformPullbackToBlowUp B S hS f b) c
          (Y.1.preimage (c ≫ b).hom)) hTcl)).map
      ((modulePullback B S hS (iteratedStrictTransformPullbackIso B S hS f b c).hom).map
        (strictTransformSheafQuotient B S hS f (c ≫ b) (Y.1.preimage (c ≫ b).hom) F))) :=
    mono_map_of_natIso (modulePullbackCompIso B S hS (openOffSubspaceι B S hS
        (strictTransformPullback B S hS (strictTransformPullbackToBlowUp B S hS f b) c)
        (exceptionalPreimageSet B S hS (strictTransformPullbackToBlowUp B S hS f b) c
          (Y.1.preimage (c ≫ b).hom)) hTcl)
      (iteratedStrictTransformPullbackIso B S hS f b c).hom).symm _ hmono1
  have hker := kernelSectionsSupportedIn_of_mono_modulePullback_map B S hS
    (openOffSubspaceι B S hS
      (strictTransformPullback B S hS (strictTransformPullbackToBlowUp B S hS f b) c)
      (exceptionalPreimageSet B S hS (strictTransformPullbackToBlowUp B S hS f b) c
        (Y.1.preimage (c ≫ b).hom)) hTcl) hjE _ hTcl
    (fun a φ hφ => factorsThrough_openOffSubspace B S hS
      (strictTransformPullback B S hS (strictTransformPullbackToBlowUp B S hS f b) c)
      (exceptionalPreimageSet B S hS (strictTransformPullbackToBlowUp B S hS f b) c
        (Y.1.preimage (c ≫ b).hom)) hTcl
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS a) φ hφ)
    (inner.inv ≫ (modulePullback B S hS
      (iteratedStrictTransformPullbackIso B S hS f b c).hom).map
        (strictTransformSheafQuotient B S hS f (c ≫ b) (Y.1.preimage (c ≫ b).hom) F))
    (by rw [Functor.map_comp]; have := hmono2; infer_instance)
  -- The universal property of the quotient by the supported sections now pins the comparison.
  obtain ⟨θ, hθ⟩ := exists_strictTransformSheafIso B S hS
    (strictTransformPullbackToBlowUp B S hS f b) c (Y.1.preimage (c ≫ b).hom)
    ((modulePullback B S hS (strictTransformPullbackToSource B S hS f b)).obj F)
    (inner.inv ≫ (modulePullback B S hS
      (iteratedStrictTransformPullbackIso B S hS f b c).hom).map
        (strictTransformSheafQuotient B S hS f (c ≫ b) (Y.1.preimage (c ≫ b).hom) F))
    hqe hker hnos
  obtain ⟨cmp, hcmp⟩ := exists_iteratedStrictTransformSheaf_iso B S hS
    (strictTransformPullbackToBlowUp B S hS f b) c Z' hc (Y.1.preimage (c ≫ b).hom)
    (exceptionalPreimageSet B S hS f b (Z.1.preimage b.hom))
    (isClosed_exceptionalPreimageSet B S hS f b _
      (isClosedSubspace_preimage B S hS b.hom Z.1 A.2 A'.2 Z.2))
    ((modulePullback B S hS (strictTransformPullbackToSource B S hS f b)).obj F)
    (exceptionalPreimageSet_compositeCentre B S hS f c hb Z' Y hY)
  refine ⟨θ.symm.trans cmp, ?_⟩
  have hkey : (modulePullback B S hS
        (iteratedStrictTransformPullbackIso B S hS f b c).hom).map
        (strictTransformSheafQuotient B S hS f (c ≫ b) (Y.1.preimage (c ≫ b).hom) F) ≫
      θ.inv =
      inner.hom ≫ strictTransformSheafQuotient B S hS
        (strictTransformPullbackToBlowUp B S hS f b) c (Y.1.preimage (c ≫ b).hom)
        ((modulePullback B S hS (strictTransformPullbackToSource B S hS f b)).obj F) := by
    rw [Iso.comp_inv_eq, Category.assoc, hθ, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  have hfin : (modulePullback B S hS
        (iteratedStrictTransformPullbackIso B S hS f b c).hom).map
        (strictTransformSheafQuotient B S hS f (c ≫ b) (Y.1.preimage (c ≫ b).hom) F) ≫
      θ.inv ≫ cmp.hom =
      inner.hom ≫ (modulePullback B S hS (strictTransformPullbackToSource B S hS
            (strictTransformPullbackToBlowUp B S hS f b) c)).map
          (strictTransformSheafQuotient B S hS f b (Z.1.preimage b.hom) F) ≫
        strictTransformSheafQuotient B S hS
          (strictTransformPullbackToBlowUp B S hS f b) c (Z'.1.preimage c.hom)
          (strictTransformSheaf B S hS f b (Z.1.preimage b.hom) F) := by
    rw [← Category.assoc, hkey, Category.assoc, hcmp]
    rfl
  exact hfin

/-- **Stacks 0868, part (2).** In the situation of part (1), the strict transform of `X` with
respect to `c` of the strict transform of `X` with respect to `b` is the strict transform of `X`
with respect to `A'' ⟶ A`: the two closed subspaces are isomorphic over the ambient base change
`X ×_A A''`.

The morphism `X' ×_{A'} A'' ⟶ X ×_A A''` of ambient base changes along which the comparison is
made is `AlgebraicGeometry.Space.iteratedStrictTransformSpaceMap`; `X'` here is the first strict
transform, the ambient base change of the second being taken over `A'` and not over `X ×_A A'`.
Its two triangles over `X` and over `A''` are the first two conjuncts of the conclusion and hold
with no hypothesis at all.

The comparison of the two closed subspaces is
`AlgebraicGeometry.Space.exists_iteratedStrictTransformSpace_iso` of
`StacksFrontier/AlgebraicGeometry/Spaces/StrictTransformSpaceComposition.lean`.  Its route is the
source's own, read on ideals: the image of the second strict transform in `(X ×_A A') ×_{A'} A''`
is a closed subspace whose defining ideal is exactly the ideal of functions supported on the
exceptional preimage of `(c ≫ b)^{-1}Y`, so it *is* the strict transform of `X` with respect to
the composite by `AlgebraicGeometry.Space.strictTransformSubfunctor_eq_of_definingIdealSheaf_eq`,
and the identification of the two ambient base changes transports that across Stacks 0863 part
(2).  One inclusion of ideals is the geometry of the two blowups (Stacks 085T through
`AlgebraicGeometry.Space.exceptionalPreimageSet_compositeCentre`, and Stacks 0862 off the
exceptional divisor); the other is Stacks 082Z together with the fact that the second strict
transform has no nonzero local function supported there, which is Stacks 083S for the two
exceptional divisors it is built from.

The conditional form of this statement in
`StacksFrontier/AlgebraicGeometry/Spaces/StrictTransformProperties.lean` keeps the name
without the suffix `_unconditional`; the suffix marks the same conclusion with that form's
assumed input discharged, and the tag is registered here. -/
@[stacks 0868 "part (2): strict transform of a space"]
theorem exists_strictTransformSpace_comp_iso_unconditional (Z : ClosedSubspaces B S hS A.1)
    (Z' : ClosedSubspaces B S hS A'.1) (Y : ClosedSubspaces B S hS A.1)
    (hb : IsBlowupAlong B S hS Z b) (hc : IsBlowupAlong B S hS Z' c)
    (hY : IsCompositeCentre B S hS b Z Z' Y) (hd : IsBlowupAlong B S hS Y (c ≫ b)) :
    ∃ (k : strictTransformPullback B S hS
          (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom)) c ⟶
        strictTransformPullback B S hS f (c ≫ b))
      (j : strictTransformSpace B S hS
          (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom)) c
          (Z'.1.preimage c.hom) ≅
        strictTransformSpace B S hS f (c ≫ b) (Y.1.preimage (c ≫ b).hom)),
      (k ≫ strictTransformPullbackToSource B S hS f (c ≫ b) =
        strictTransformPullbackToSource B S hS
            (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom)) c ≫
          strictTransformSpaceι B S hS f b (Z.1.preimage b.hom) ≫
            strictTransformPullbackToSource B S hS f b) ∧
      (k ≫ strictTransformPullbackToBlowUp B S hS f (c ≫ b) =
        strictTransformPullbackToBlowUp B S hS
          (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom)) c) ∧
      j.hom ≫ strictTransformSpaceι B S hS f (c ≫ b) (Y.1.preimage (c ≫ b).hom) =
        strictTransformSpaceι B S hS
            (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom)) c
            (Z'.1.preimage c.hom) ≫ k :=
  let ⟨j, hj⟩ := exists_iteratedStrictTransformSpace_iso B S hS f b c Z Z' Y hb hc hY hd
  ⟨iteratedStrictTransformSpaceMap B S hS f b c (Z.1.preimage b.hom), j,
    iteratedStrictTransformSpaceMap_toSource B S hS f b c (Z.1.preimage b.hom),
    iteratedStrictTransformSpaceMap_toBlowUp B S hS f b c (Z.1.preimage b.hom), hj⟩

end Composition

end AlgebraicGeometry.Space

end
