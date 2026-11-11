module

public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningFunctor.EtaleLocalRepresentability
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningFunctors.IsomorphismLimit
public import StacksFrontier.AlgebraicGeometry.Flatness.IsomorphismFunctorRepresentability
public import StacksFrontier.AlgebraicGeometry.Limits.LimitPreservingFunctorOfPoints

/-!
# The isomorphism locus of a module map is detected on affine test schemes

Let `f : X ⟶ S` be a morphism of schemes and `u : F ⟶ G` a homomorphism of quasi-coherent
modules on `X`.  `Stacks.Flatness.ModuleMapBaseChangeSituation.isomorphismFunctor` is the
subterminal functor on schemes over `S` recording where the base change of `u` becomes an
isomorphism.

An ideal sheaf on the base cutting out the isomorphism locus on affine schemes over the base cuts
it out on all of them: containment of the ideal sheaf in the kernel of a structure morphism is
equivalent to factoring through the closed subscheme it cuts out, and that criterion is tested on
an affine open cover, where the isomorphism condition is Zariski local — a special case of the
fpqc sheaf property of Tag 05MJ.  This is the form in which the flattening ideal of Tag 05PE
presents itself.

The two assertions of Tag 05PF are then assembled.  Representability by a closed immersion is the
devissage carried out in
`Stacks.Flatness.exists_closedImmersion_representableBy_isomorphismFunctor`.  Finite presentation
of a representing closed immersion needs no hypothesis beyond the source's own: the functor is
limit preserving in the sense of Tag 05LX when `F` is of finite type and `G` of finite
presentation, by Tag 05MJ(4), so its representing morphism is locally of finite presentation by
Tag 01ZC; quasi-compactness holds because a closed immersion is affine, and quasi-separatedness
because a representing morphism is a monomorphism.

## Main definitions

* `Stacks.Flatness.ModuleMapBaseChangeSituation.IsFlatteningIdealOnAffines` is the condition that
  an ideal sheaf on the base cut out the isomorphism locus on affine schemes over the base.

## Main results

* `Stacks.Flatness.ModuleMapBaseChangeSituation.isFlatteningIdeal_of_isFlatteningIdealOnAffines`:
  an ideal sheaf detecting the isomorphism locus on affine test schemes detects it everywhere.
* `Stacks.Flatness.isomorphismFunctor_representableBy_closedImmersion_of_affineTests` and
  `Stacks.Flatness.finitePresentation_hom_of_representableBy_isomorphismFunctor`: the two
  assertions of Tag 05PF, separately.
* `Stacks.Flatness.exists_closedImmersion_representableBy_isomorphismFunctor_finitePresentation`:
  Tag 05PF, both assertions under the source's assumptions.

## Implementation notes

The values of `isomorphismFunctor` lie in `Type 0` while the morphisms of `Over S` lie in
`Type u`, so the comparison with a functor of points goes through
`CategoryTheory.uliftFunctor`; `CategoryTheory.Functor.RepresentableBy` is universe
heterogeneous, so the lifted representability is built by transporting the bijections along
`Equiv.ulift`.

## References

* [Stacks Project, Tag 05MJ](https://stacks.math.columbia.edu/tag/05MJ)
* [Stacks Project, Tag 05PE](https://stacks.math.columbia.edu/tag/05PE)
* [Stacks Project, Tag 05PF](https://stacks.math.columbia.edu/tag/05PF)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Flatness.ModuleMapBaseChangeSituation

variable (D : ModuleMapBaseChangeSituation.{u})

/-- An ideal sheaf on the base is a *flattening ideal on affines* for the situation when it
detects the locus where the base change of `u` is an isomorphism on affine schemes over the base:
an affine scheme over `S` makes `u` an isomorphism exactly when the ideal sheaf is contained in
the kernel of its structure morphism. -/
abbrev IsFlatteningIdealOnAffines (J : D.S.IdealSheafData) : Prop :=
  ∀ T : Over D.S, IsAffine T.left → (D.IsIsomorphismAfterBaseChange T ↔ J ≤ T.hom.ker)

/-- **An ideal sheaf detecting the isomorphism locus on affine test schemes detects it
everywhere.**  Containment of the ideal sheaf in the kernel of a structure morphism is
equivalent to factoring through the closed subscheme it cuts out, and that criterion is tested on
affine schemes. -/
theorem isFlatteningIdeal_of_isFlatteningIdealOnAffines {J : D.S.IdealSheafData}
    (hJ : D.IsFlatteningIdealOnAffines J) : D.IsFlatteningIdeal J := by
  have key : D.IsoFactorizationCriterion J.subschemeι :=
    D.isoFactorizationCriterion_of_affineTests J.subschemeι inferInstance fun T hT ↦ by
      rw [hJ T hT, Scheme.Hom.exists_comp_eq_iff_ker_le J.subschemeι T.hom,
        Scheme.IdealSheafData.ker_subschemeι]
  intro T
  rw [key T, Scheme.Hom.exists_comp_eq_iff_ker_le J.subschemeι T.hom,
    Scheme.IdealSheafData.ker_subschemeι]

/-- Testing on affine schemes over the base is no weaker than testing on all of them. -/
theorem isFlatteningIdeal_iff_isFlatteningIdealOnAffines (J : D.S.IdealSheafData) :
    D.IsFlatteningIdeal J ↔ D.IsFlatteningIdealOnAffines J :=
  ⟨fun hJ T _ ↦ hJ T, D.isFlatteningIdeal_of_isFlatteningIdealOnAffines⟩

/-- The isomorphism functor, with values lifted to the universe of the morphisms of the category
of schemes over the base, is represented by the same object. -/
noncomputable def representableByULift {W : Over D.S}
    (e : D.isomorphismFunctor.RepresentableBy W) :
    (D.isomorphismFunctor ⋙ uliftFunctor.{u}).RepresentableBy W where
  homEquiv := e.homEquiv.trans Equiv.ulift.symm
  homEquiv_comp f g := by
    apply ULift.ext
    exact e.homEquiv_comp f g

end Stacks.Flatness.ModuleMapBaseChangeSituation

namespace Stacks.Flatness

/-- The isomorphism-after-base-change functor of a surjection from a finitely presented, flat and
pure module is represented by a closed immersion into the base: the first assertion of Tag 05PF,
which together with the second is
`Stacks.Flatness.exists_closedImmersion_representableBy_isomorphismFunctor_finitePresentation`.

The representing closed subscheme is cut out by an ideal sheaf which it suffices to exhibit on
*affine* schemes over the base, by
`Stacks.Flatness.ModuleMapBaseChangeSituation.isFlatteningIdeal_of_isFlatteningIdealOnAffines`;
étale localization on the base reduces the construction to an affine situation whose module of
sections is projective, where the ideal sheaf is the flattening ideal of Tag 05PE.  That
devissage is
`Stacks.Flatness.exists_closedImmersion_representableBy_isomorphismFunctor`. -/
theorem isomorphismFunctor_representableBy_closedImmersion_of_affineTests
    (D : ModuleMapBaseChangeSituation.{u})
    [LocallyOfFinitePresentation D.f] [QuasiCompact D.f] [QuasiSeparated D.f]
    [D.F.IsFinitePresentation] [D.F.IsFiniteType] [Epi D.hom]
    (hflat : IsFlatOver D.f.toLRSHom.toShHom D.F)
    (hpure : IsPureRelative D.f D.F) :
    ∃ W : Over D.S, IsClosedImmersion W.hom ∧
      Nonempty (D.isomorphismFunctor.RepresentableBy W) :=
  exists_closedImmersion_representableBy_isomorphismFunctor D hflat hpure

/-- A closed immersion `Z ⟶ S` representing the isomorphism-after-base-change functor is of
finite presentation as soon as the target module `G` is of finite presentation: the second
assertion of Tag 05PF, assembled with the first in
`Stacks.Flatness.exists_closedImmersion_representableBy_isomorphismFunctor_finitePresentation`.

Local finite presentation is Tag 01ZC: by Tag 05MJ(4) the isomorphism functor turns a cofiltered
inverse limit of affine schemes over the base into a filtered colimit, so the functor of points
of `Z` is limit preserving in the sense of Tag 05LX.  Quasi-compactness holds because a closed
immersion is an affine morphism, and quasi-separatedness because the functor is subterminal, so
that `Z ⟶ S` is a monomorphism.

The hypotheses are about the morphism `i` at hand, and they are satisfiable: a closed immersion
representing the functor exists under the source's own hypotheses, by
`Stacks.Flatness.isomorphismFunctor_representableBy_closedImmersion_of_affineTests`.  Stating the
assertion for an arbitrary representative rather than for that one is no weaker, since any two
representatives of a functor are isomorphic over the base. -/
theorem finitePresentation_hom_of_representableBy_isomorphismFunctor
    (D : ModuleMapBaseChangeSituation.{u}) [QuasiCompact D.f]
    [D.F.IsFiniteType] [D.G.IsFinitePresentation]
    {Z : Scheme.{u}} (i : Z ⟶ D.S) [IsClosedImmersion i]
    (e : D.isomorphismFunctor.RepresentableBy (Over.mk i)) :
    FinitePresentation i := by
  have hlfp : LocallyOfFinitePresentation i := by
    refine (Scheme.locallyOfFinitePresentation_iff_isLimitPreserving_yoneda i).2 ?_
    intro I _ _ T hT
    have hpres : PreservesColimit T.op D.isomorphismFunctor :=
      D.isomorphismFunctor_preservesColimit_of_isAffine I T hT
    have hlift : PreservesColimit T.op (D.isomorphismFunctor ⋙ uliftFunctor.{u}) :=
      inferInstance
    exact (preservesColimit_iff_of_natIso T.op (D.representableByULift e).toIso).2 hlift
  have hmono : Mono i := mono_hom_of_representableBy e
  exact FinitePresentation.mk hlfp inferInstance inferInstance

/-- **Stacks Project, Tag 05PF.** Let `f : X ⟶ S` be a morphism of finite presentation (locally
of finite presentation, quasi-compact and quasi-separated, Tag 01TP) and let `u : F ⟶ G` be a
surjection of quasi-coherent modules on `X` with `F` of finite presentation, flat over `S` and
pure relative to `S`.  Then the functor `F_iso` on schemes over `S`, whose value at
`T` is a point exactly when the base change `u_T` is an isomorphism, is represented by a closed
immersion `Z ⟶ S`; moreover `Z ⟶ S` is of finite presentation if `G` is of finite presentation.

The representing closed immersion comes from the étale-local devissage
`Stacks.Flatness.exists_closedImmersion_representableBy_isomorphismFunctor`: purity reduces the
question étale locally on `S` to an affine situation with projective sections, cut out by the
flattening ideal of Tag 05PE, and the local closed subschemes glue by fpqc descent (Tags 05MJ,
03I0).  Its finite presentation is
`Stacks.Flatness.finitePresentation_hom_of_representableBy_isomorphismFunctor`, from Tag 05MJ(4)
and Tag 05LX.

The instance `F.IsFiniteType` is part of the statement because purity relative to `S` is phrased
for modules of finite type; it follows from `F.IsFinitePresentation` by
`Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isFinitePresentation`, so
it adds nothing to the source's assumptions. -/
@[stacks 05PF "both assertions: representability by a closed immersion, which is of finite \
  presentation when `G` is"]
theorem exists_closedImmersion_representableBy_isomorphismFunctor_finitePresentation
    (D : ModuleMapBaseChangeSituation.{u})
    [LocallyOfFinitePresentation D.f] [QuasiCompact D.f] [QuasiSeparated D.f]
    [D.F.IsFinitePresentation] [D.F.IsFiniteType] [Epi D.hom]
    (hflat : IsFlatOver D.f.toLRSHom.toShHom D.F)
    (hpure : IsPureRelative D.f D.F) :
    ∃ W : Over D.S, IsClosedImmersion W.hom ∧
      Nonempty (D.isomorphismFunctor.RepresentableBy W) ∧
      (D.G.IsFinitePresentation → FinitePresentation W.hom) := by
  obtain ⟨W, hW, ⟨e⟩⟩ := exists_closedImmersion_representableBy_isomorphismFunctor D hflat hpure
  refine ⟨W, hW, ⟨e⟩, fun hG ↦ ?_⟩
  have : IsClosedImmersion W.hom := hW
  exact finitePresentation_hom_of_representableBy_isomorphismFunctor D W.hom e

end Stacks.Flatness

end
